-- Prove2me | solution 1 for CarlenKusuokaStroock.heatKernel_le_exp_davies
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:42:10.441974+00:00
-- url     : https://prove2.me/submissions/af58a328-5cf3-4766-9a29-ee3f06d7cf5f

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
universe u

section
/-!
# Kernel library for the Markov heat-kernel package

Substochastic kernels on a type `X` (no countability needed): non-negative entries, summable rows
with sums at most one. Their powers `stepProb`, Chapman–Kolmogorov, symmetry of powers, column
sums, and Poisson series facts used by the heat kernel.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

/-- A substochastic kernel. -/
def IsSub (p : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ p x y) ∧ (∀ x, Summable (p x)) ∧ ∀ x, ∑' y, p x y ≤ 1

lemma isSub_of_isTransition {p : X → X → ℝ} (h : IsTransition p) : IsSub p :=
  ⟨h.1, h.2.1, fun x => (h.2.2 x).le⟩

lemma IsSub.le_one {p : X → X → ℝ} (h : IsSub p) (x y : X) : p x y ≤ 1 :=
  le_trans ((h.2.1 x).le_tsum y fun z _ => h.1 x z) (h.2.2 x)

/-- Fubini for `a(w) q(w, z) r(z)`, `a ≥ 0` summable, `q` substochastic, `0 ≤ r ≤ 1`. -/
lemma summable_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    Summable (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := by
  have h0 : 0 ≤ (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := fun p =>
    mul_nonneg (mul_nonneg (ha0 _) (hq.1 _ _)) (hr0 _)
  have hrow : ∀ w, Summable (fun z => a w * q w z * r z) := fun w =>
    Summable.of_nonneg_of_le (fun z => h0 (w, z))
      (fun z => by
        have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
        simpa using this)
      ((hq.2.1 w).mul_left (a w))
  refine (summable_prod_of_nonneg h0).mpr ⟨hrow, ?_⟩
  refine Summable.of_nonneg_of_le (fun w => tsum_nonneg fun z => h0 (w, z)) (fun w => ?_) has
  calc ∑' z, a w * q w z * r z ≤ ∑' z, a w * q w z :=
        Summable.tsum_le_tsum (fun z => by
          have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
          simpa using this) (hrow w) ((hq.2.1 w).mul_left (a w))
    _ = a w * ∑' z, q w z := tsum_mul_left
    _ ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
    _ = a w := mul_one _

/-- Exchange of the order of summation for `a(w) q(w, z) r(z)`. -/
lemma tsum_comm_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    ∑' w, a w * ∑' z, q w z * r z = ∑' z, (∑' w, a w * q w z) * r z := by
  have hs := summable_triple ha0 has hq hr0 hr1
  have hcomm := Summable.tsum_comm (f := fun w z => a w * q w z * r z) hs
  have hcol : ∀ z, Summable (fun w => a w * q w z * r z) :=
    fun z => hs.prod_symm.prod_factor z
  calc ∑' w, a w * ∑' z, q w z * r z = ∑' w, ∑' z, a w * q w z * r z := by
        refine tsum_congr fun w => ?_
        rw [← tsum_mul_left]; exact tsum_congr fun z => by ring
    _ = ∑' z, ∑' w, a w * q w z * r z := hcomm.symm
    _ = ∑' z, (∑' w, a w * q w z) * r z := by
        refine tsum_congr fun z => ?_
        rw [← tsum_mul_right]

/-- The weighted column sums `z ↦ ∑_w a(w) q(w, z)` are summable with total `≤ ∑ a`. -/
lemma summable_col {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) :
    Summable (fun z => ∑' w, a w * q w z) ∧ (∀ z, Summable (fun w => a w * q w z)) ∧
      ∑' z, ∑' w, a w * q w z ≤ ∑' w, a w := by
  have hs := summable_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
  simp only [mul_one] at hs
  refine ⟨?_, fun z => ?_, ?_⟩
  · have := hs.prod_symm.prod
    simpa using this
  · have := hs.prod_symm.prod_factor z
    simpa using this
  · have h := tsum_comm_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one] at h
    rw [← h]
    refine Summable.tsum_le_tsum (fun w => ?_) ?_ has
    · calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _
    · refine Summable.of_nonneg_of_le (fun w => mul_nonneg (ha0 w) (tsum_nonneg (hq.1 w)))
        (fun w => ?_) has
      calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _

variable [DecidableEq X]

lemma stepProb_zero (p : X → X → ℝ) (x y : X) :
    stepProb p 0 x y = if x = y then 1 else 0 := rfl

lemma stepProb_succ (p : X → X → ℝ) (n : ℕ) (x y : X) :
    stepProb p (n + 1) x y = ∑' z, p x z * stepProb p n z y := rfl

lemma isSub_stepProb {p : X → X → ℝ} (hp : IsSub p) : ∀ n, IsSub (stepProb p n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun x y => by simp only [stepProb_zero]; split_ifs <;> norm_num, fun x => ?_,
      fun x => ?_⟩
    · exact (hasSum_ite_eq x (1 : ℝ)).summable.congr fun y => by
        simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
    · have : (fun y => stepProb p 0 x y) = fun y => if y = x then 1 else 0 := by
        funext y; simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
      rw [this, tsum_ite_eq]
  | succ n ih =>
    refine ⟨fun x y => tsum_nonneg fun z => mul_nonneg (hp.1 x z) (ih.1 z y), fun x => ?_,
      fun x => ?_⟩
    · exact (summable_col (hp.1 x) (hp.2.1 x) ih).1
    · exact le_trans (summable_col (hp.1 x) (hp.2.1 x) ih).2.2 (hp.2.2 x)

lemma stepProb_nonneg {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    0 ≤ stepProb p n x y := (isSub_stepProb hp n).1 x y

lemma stepProb_le_one {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    stepProb p n x y ≤ 1 := (isSub_stepProb hp n).le_one x y

/-- Chapman–Kolmogorov. -/
lemma stepProb_add {p : X → X → ℝ} (hp : IsSub p) (m n : ℕ) (x y : X) :
    stepProb p (m + n) x y = ∑' z, stepProb p m x z * stepProb p n z y := by
  induction m generalizing x with
  | zero =>
    simp only [zero_add, stepProb_zero]
    have : (fun z => (if x = z then (1 : ℝ) else 0) * stepProb p n z y) =
        fun z => if z = x then stepProb p n x y else 0 := by
      funext z; split_ifs <;> simp_all [eq_comm]
    rw [this, tsum_ite_eq]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, stepProb_succ]
    simp only [ih]
    have := tsum_comm_triple (hp.1 x) (hp.2.1 x) (isSub_stepProb hp m)
      (r := fun z => stepProb p n z y) (fun z => stepProb_nonneg hp n z y)
      (fun z => stepProb_le_one hp n z y)
    rw [this]
    rfl

lemma stepProb_one {p : X → X → ℝ} (x y : X) : stepProb p 1 x y = p x y := by
  simp only [stepProb_succ, stepProb_zero]
  have : (fun z => p x z * (if z = y then (1 : ℝ) else 0)) = fun z => if z = y then p x y else 0 := by
    funext z; split_ifs with h <;> simp [h]
  rw [this, tsum_ite_eq]

/-- Right peeling: `pⁿ⁺¹(x, y) = ∑_z pⁿ(x, z) p(z, y)`. -/
lemma stepProb_succ' {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    stepProb p (n + 1) x y = ∑' z, stepProb p n x z * p z y := by
  rw [stepProb_add hp n 1]
  simp only [stepProb_one]

/-- Powers of a symmetric kernel are symmetric. -/
lemma stepProb_symm {p : X → X → ℝ} (hp : IsSub p) (hs : IsSymmetric p) (n : ℕ) (x y : X) :
    stepProb p n x y = stepProb p n y x := by
  induction n generalizing x y with
  | zero => simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
  | succ n ih =>
    rw [stepProb_succ, stepProb_succ' hp]
    refine tsum_congr fun z => ?_
    rw [hs x z, ih z y, mul_comm]

/-! ## The heat kernel -/

lemma uniformize_eq_self {J : X → X → ℝ} (hJ : IsTransition J) : uniformize J = J := by
  funext a b; simp [uniformize, hJ.2.2 a]

/-- The Poisson weights. -/
noncomputable def poi (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t) * t ^ n / n.factorial

lemma poi_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poi t n := by
  unfold poi; positivity

lemma hasSum_poi (t : ℝ) : HasSum (poi t) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp t
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-t))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have e : poi t = fun i => Real.exp (-t) * (t ^ i / ↑i.factorial) := by
    funext n; unfold poi; ring
  rw [e]; exact h2

lemma summable_poi (t : ℝ) : Summable (poi t) := (hasSum_poi t).summable

lemma tsum_poi (t : ℝ) : ∑' n, poi t n = 1 := (hasSum_poi t).tsum_eq

/-- `∑ n poi(t, n) = t`. -/
lemma hasSum_poi_mul (t : ℝ) : HasSum (fun n => poi t n * n) t := by
  have h := (hasSum_poi t).mul_left t
  rw [mul_one] at h
  -- shift: poi t (n+1) * (n+1) = t * poi t n
  have hshift : ∀ n : ℕ, poi t (n + 1) * ((n + 1 : ℕ) : ℝ) = t * poi t n := by
    intro n
    unfold poi
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have e : (fun n => poi t (n + 1) * ((n + 1 : ℕ) : ℝ)) = fun n => t * poi t n := by
    funext n; exact hshift n
  rw [e]; exact h

lemma summable_poi_mul (t : ℝ) : Summable (fun n => poi t n * n) := (hasSum_poi_mul t).summable

lemma heatKernel_eq {J : X → X → ℝ} (t : ℝ) (x y : X) :
    heatKernel J t x y = ∑' n, poi t n * stepProb (uniformize J) n x y := rfl

lemma summable_heat {p : X → X → ℝ} (hp : IsSub p) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    Summable (fun n => poi t n * stepProb p n x y) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (poi_nonneg ht n) (stepProb_nonneg hp n x y))
    (fun n => by
      have := mul_le_mul_of_nonneg_left (stepProb_le_one hp n x y) (poi_nonneg ht n)
      simpa using this)
    (summable_poi t)

end MarkovHK
end

section
/-!
# Near and far parts of a kernel; `uniformize` of a substochastic kernel (shared by H6 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

lemma nearPart_nonneg {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (x y : X) :
    0 ≤ nearPart J ρ R x y := by
  unfold nearPart; split_ifs
  · exact hJ.1 x y
  · exact le_rfl

lemma nearPart_le {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (x y : X) :
    nearPart J ρ R x y ≤ J x y := by
  unfold nearPart; split_ifs
  · exact le_rfl
  · exact hJ.1 x y

lemma summable_nearPart {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (x : X) :
    Summable (nearPart J ρ R x) :=
  Summable.of_nonneg_of_le (nearPart_nonneg hJ R x) (nearPart_le hJ R x) (hJ.2.1 x)

lemma tsum_nearPart_le {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (x : X) :
    ∑' y, nearPart J ρ R x y ≤ 1 := by
  rw [← hJ.2.2 x]
  exact Summable.tsum_le_tsum (nearPart_le hJ R x) (summable_nearPart hJ R x) (hJ.2.1 x)

lemma nearPart_symm {J ρ : X → X → ℝ} (hJs : IsSymmetric J) (hρ : IsMetric ρ) (R : ℝ) :
    IsSymmetric (nearPart J ρ R) := by
  intro x y; unfold nearPart; rw [hρ.symm x y, hJs x y]

variable [DecidableEq X]

/-- `uniformize` of a substochastic kernel is a transition kernel. -/
lemma isTransition_uniformize {K : X → X → ℝ} (hK0 : ∀ x y, 0 ≤ K x y) (hKs : ∀ x, Summable (K x))
    (hK1 : ∀ x, ∑' y, K x y ≤ 1) : IsTransition (uniformize K) := by
  have hite : ∀ x, Summable (fun y => if x = y then 1 - ∑' z, K x z else 0) := by
    intro x
    exact (hasSum_ite_eq x (1 - ∑' z, K x z)).summable.congr fun y => by
      split_ifs <;> simp_all [eq_comm]
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · unfold uniformize
    have := hK0 x y
    split_ifs
    · linarith [hK1 x]
    · linarith
  · exact (hKs x).add (hite x)
  · unfold uniformize
    rw [(hKs x).tsum_add (hite x)]
    have : ∑' y, (if x = y then 1 - ∑' z, K x z else 0) = 1 - ∑' z, K x z := by
      rw [show (fun y => if x = y then 1 - ∑' z, K x z else 0) =
        fun y => if y = x then 1 - ∑' z, K x z else 0 by funext y; split_ifs <;> simp_all [eq_comm]]
      exact tsum_ite_eq x _
    rw [this]; ring

lemma uniformize_symm {K : X → X → ℝ} (hKs : IsSymmetric K) : IsSymmetric (uniformize K) := by
  intro x y; unfold uniformize
  by_cases h : x = y
  · subst h; rfl
  · simp [h, Ne.symm h, hKs x y]

end MarkovHK
end

section
/-!
# Binomial and shifted-exponential identities (shared by H9 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*} [DecidableEq X]

end MarkovHK
end

section
/-!
# Heat kernels of transition kernels: semigroup law, off-diagonal bound, comparison

* `heat_semigroup`: `∑_w p(s, u, w) p(s', w, v) = p(s + s', u, v)`;
* `heat_le_avg_diag`: for symmetric `J`, `p(t, u, v) ≤ (p(t, u, u) + p(t, v, v)) / 2`;
* `heat_le_exp_mul_heat`: if `A ≤ B + δ I` entrywise (both transition kernels), then
  `p_A(t) ≤ e^{δt} p_B(t)` entrywise.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

/-! ## Fubini across two index types -/

section Gen

variable {α β : Type*}

lemma summable_triple_gen {a : α → ℝ} (ha0 : ∀ i, 0 ≤ a i) (has : Summable a) {q : α → β → ℝ}
    (hq0 : ∀ i w, 0 ≤ q i w) (hqs : ∀ i, Summable (q i)) (hq1 : ∀ i, ∑' w, q i w ≤ 1)
    {r : β → ℝ} (hr0 : ∀ w, 0 ≤ r w) (hr1 : ∀ w, r w ≤ 1) :
    Summable (fun p : α × β => a p.1 * q p.1 p.2 * r p.2) := by
  have h0 : 0 ≤ (fun p : α × β => a p.1 * q p.1 p.2 * r p.2) := fun p =>
    mul_nonneg (mul_nonneg (ha0 _) (hq0 _ _)) (hr0 _)
  have hle : ∀ i w, a i * q i w * r w ≤ a i * q i w := fun i w => by
    have := mul_le_mul_of_nonneg_left (hr1 w) (mul_nonneg (ha0 i) (hq0 i w))
    simpa using this
  have hrow : ∀ i, Summable (fun w => a i * q i w * r w) := fun i =>
    Summable.of_nonneg_of_le (fun w => h0 (i, w)) (hle i) ((hqs i).mul_left (a i))
  refine (summable_prod_of_nonneg h0).mpr ⟨hrow, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun w => h0 (i, w)) (fun i => ?_) has
  calc ∑' w, a i * q i w * r w ≤ ∑' w, a i * q i w :=
        Summable.tsum_le_tsum (hle i) (hrow i) ((hqs i).mul_left (a i))
    _ = a i * ∑' w, q i w := tsum_mul_left
    _ ≤ a i * 1 := mul_le_mul_of_nonneg_left (hq1 i) (ha0 i)
    _ = a i := mul_one _

lemma tsum_comm_gen {a : α → ℝ} (ha0 : ∀ i, 0 ≤ a i) (has : Summable a) {q : α → β → ℝ}
    (hq0 : ∀ i w, 0 ≤ q i w) (hqs : ∀ i, Summable (q i)) (hq1 : ∀ i, ∑' w, q i w ≤ 1)
    {r : β → ℝ} (hr0 : ∀ w, 0 ≤ r w) (hr1 : ∀ w, r w ≤ 1) :
    ∑' i, a i * ∑' w, q i w * r w = ∑' w, (∑' i, a i * q i w) * r w := by
  have hs := summable_triple_gen ha0 has hq0 hqs hq1 hr0 hr1
  have hcomm := Summable.tsum_comm (f := fun i w => a i * q i w * r w) hs
  calc ∑' i, a i * ∑' w, q i w * r w = ∑' i, ∑' w, a i * q i w * r w := by
        refine tsum_congr fun i => ?_
        rw [← tsum_mul_left]; exact tsum_congr fun w => by ring
    _ = ∑' w, ∑' i, a i * q i w * r w := hcomm.symm
    _ = ∑' w, (∑' i, a i * q i w) * r w := by
        refine tsum_congr fun w => ?_
        rw [← tsum_mul_right]

lemma summable_col_gen {a : α → ℝ} (ha0 : ∀ i, 0 ≤ a i) (has : Summable a) {q : α → β → ℝ}
    (hq0 : ∀ i w, 0 ≤ q i w) (hqs : ∀ i, Summable (q i)) (hq1 : ∀ i, ∑' w, q i w ≤ 1) :
    Summable (fun w => ∑' i, a i * q i w) := by
  have hs := summable_triple_gen ha0 has hq0 hqs hq1 (r := fun _ => 1) (fun _ => zero_le_one)
    (fun _ => le_rfl)
  simp only [mul_one] at hs
  simpa using hs.prod_symm.prod

end Gen

/-- A summable function on `ℕ × ℕ` sums along antidiagonals. -/
lemma tsum_prod_antidiagonal {F : ℕ × ℕ → ℝ} (hF : Summable F) :
    ∑' p, F p = ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F]
  have hs : Summable (F ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) :=
    (Equiv.summable_iff _).mpr hF
  have h2 := hs.tsum_sigma' (fun n => (hasSum_fintype _).summable)
  simp only [Function.comp_apply] at h2
  rw [h2]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  exact Finset.sum_coe_sort _ _

/-- The Poisson convolution `∑_{a+b=n} poi(s, a) poi(s', b) = poi(s + s', n)`. -/
lemma poi_conv (s s' : ℝ) (n : ℕ) :
    ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, poi s kl.1 * poi s' kl.2 = poi (s + s') n := by
  unfold poi
  rw [(Commute.all s s').add_pow', Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hkl' : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  have hc : (n.choose kl.1 : ℝ) * kl.1.factorial * kl.2.factorial = n.factorial := by
    have h0 := Nat.add_choose_mul_factorial_mul_factorial kl.2 kl.1
    rw [add_comm kl.2 kl.1, hkl'] at h0
    have h0' : n.choose kl.1 * kl.1.factorial * kl.2.factorial = n.factorial := by
      rw [← h0]; ring
    exact_mod_cast h0'
  have h4 : (n.choose kl.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h1 : (kl.1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (kl.2.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [nsmul_eq_mul, ← hc, neg_add, Real.exp_add]
  field_simp

variable {X : Type*} [DecidableEq X]

lemma heat_nonneg {J : X → X → ℝ} (hJ : IsTransition J) {t : ℝ} (ht : 0 ≤ t) (u v : X) :
    0 ≤ heatKernel J t u v := by
  rw [heatKernel_eq, uniformize_eq_self hJ]
  exact tsum_nonneg fun n => mul_nonneg (poi_nonneg ht n)
    (stepProb_nonneg (isSub_of_isTransition hJ) n u v)

lemma heat_le_one {J : X → X → ℝ} (hJ : IsTransition J) {t : ℝ} (ht : 0 ≤ t) (u v : X) :
    heatKernel J t u v ≤ 1 := by
  rw [heatKernel_eq, uniformize_eq_self hJ, ← tsum_poi t]
  have hS := isSub_of_isTransition hJ
  exact Summable.tsum_le_tsum (fun n => by
    have := mul_le_mul_of_nonneg_left (stepProb_le_one hS n u v) (poi_nonneg ht n)
    simpa using this) (summable_heat hS ht u v) (summable_poi t)

lemma heat_symm {J : X → X → ℝ} (hJ : IsTransition J) (hJs : IsSymmetric J) (t : ℝ) (u v : X) :
    heatKernel J t u v = heatKernel J t v u := by
  rw [heatKernel_eq, heatKernel_eq, uniformize_eq_self hJ]
  exact tsum_congr fun n => by rw [stepProb_symm (isSub_of_isTransition hJ) hJs]

/-- Rows of the heat kernel are summable (with sum one). -/
lemma summable_heat_row {J : X → X → ℝ} (hJ : IsTransition J) {t : ℝ} (ht : 0 ≤ t) (u : X) :
    Summable (fun w => heatKernel J t u w) := by
  have hS := isSub_of_isTransition hJ
  have := summable_col_gen (poi_nonneg ht) (summable_poi t) (q := fun n w => stepProb J n u w)
    (fun n w => stepProb_nonneg hS n u w) (fun n => (isSub_stepProb hS n).2.1 u)
    (fun n => (isSub_stepProb hS n).2.2 u)
  refine this.congr fun w => ?_
  rw [heatKernel_eq, uniformize_eq_self hJ]

/-- The semigroup law. -/
lemma heat_semigroup {J : X → X → ℝ} (hJ : IsTransition J) {s s' : ℝ} (hs : 0 ≤ s)
    (hs' : 0 ≤ s') (u v : X) :
    ∑' w, heatKernel J s u w * heatKernel J s' w v = heatKernel J (s + s') u v := by
  have hS := isSub_of_isTransition hJ
  simp only [heatKernel_eq, uniformize_eq_self hJ]
  -- step 1: pull the sum over `a` out
  have step1 := tsum_comm_gen (poi_nonneg hs) (summable_poi s)
    (q := fun a w => stepProb J a u w) (fun a w => stepProb_nonneg hS a u w)
    (fun a => (isSub_stepProb hS a).2.1 u) (fun a => (isSub_stepProb hS a).2.2 u)
    (r := fun w => ∑' b, poi s' b * stepProb J b w v)
    (fun w => by have := heat_nonneg hJ hs' w v; rwa [heatKernel_eq, uniformize_eq_self hJ] at this)
    (fun w => by have := heat_le_one hJ hs' w v; rwa [heatKernel_eq, uniformize_eq_self hJ] at this)
  rw [← step1]
  -- step 2: inside, pull the sum over `b` out
  have step2 : ∀ a, ∑' w, stepProb J a u w * ∑' b, poi s' b * stepProb J b w v =
      ∑' b, poi s' b * stepProb J (a + b) u v := by
    intro a
    have h := tsum_comm_gen (fun w => stepProb_nonneg hS a u w) ((isSub_stepProb hS a).2.1 u)
      (q := fun w b => poi s' b * stepProb J b w v)
      (fun w b => mul_nonneg (poi_nonneg hs' b) (stepProb_nonneg hS b w v))
      (fun w => summable_heat hS hs' w v)
      (fun w => by have := heat_le_one hJ hs' w v; rwa [heatKernel_eq, uniformize_eq_self hJ] at this)
      (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one] at h
    rw [h]
    refine tsum_congr fun b => ?_
    rw [stepProb_add hS a b u v, ← tsum_mul_left]
    exact tsum_congr fun w => by ring
  simp only [step2]
  -- step 3: the double series over `ℕ × ℕ`
  have hrow' : ∀ a, Summable (fun b => poi s' b * stepProb J (a + b) u v) := fun a =>
    Summable.of_nonneg_of_le (fun b => mul_nonneg (poi_nonneg hs' b) (stepProb_nonneg hS _ u v))
      (fun b => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hS (a + b) u v) (poi_nonneg hs' b)
        simpa using this) (summable_poi s')
  set G : ℕ × ℕ → ℝ := fun p => poi s p.1 * (poi s' p.2 * stepProb J (p.1 + p.2) u v) with hG
  have hG0 : 0 ≤ G := fun p => mul_nonneg (poi_nonneg hs _)
    (mul_nonneg (poi_nonneg hs' _) (stepProb_nonneg hS _ u v))
  have hGrow : ∀ a, Summable (fun b => G (a, b)) := fun a => (hrow' a).mul_left (poi s a)
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨hGrow, ?_⟩
    refine Summable.of_nonneg_of_le (fun a => tsum_nonneg fun b => hG0 (a, b)) (fun a => ?_)
      (summable_poi s)
    calc ∑' b, G (a, b) = poi s a * ∑' b, poi s' b * stepProb J (a + b) u v := by
          rw [← tsum_mul_left]
      _ ≤ poi s a * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (poi_nonneg hs a)
          rw [← tsum_poi s']
          refine Summable.tsum_le_tsum (fun b => ?_) (hrow' a) (summable_poi s')
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hS (a + b) u v) (poi_nonneg hs' b)
          simpa using this
      _ = poi s a := mul_one _
  calc ∑' a, poi s a * ∑' b, poi s' b * stepProb J (a + b) u v
      = ∑' a, ∑' b, G (a, b) := tsum_congr fun a => by rw [← tsum_mul_left]
    _ = ∑' p, G p := hGs.tsum_prod.symm
    _ = ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, G kl := tsum_prod_antidiagonal hGs
    _ = ∑' n, poi (s + s') n * stepProb J n u v := by
        refine tsum_congr fun n => ?_
        rw [← poi_conv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        have hkl' : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
        simp only [hG, hkl']
        ring

end MarkovHK
end

section
/-!
# H5, reduced to the core ℓ² estimate of Carlen–Kusuoka–Stroock (no `sorry`)

`CoreL2` is the `L² → L^∞` (equivalently, column-`ℓ²`) bound for the Davies-twisted heat
semigroup `K^ψ_s(z, y) = e^{−ψ(z)} p_R(s, z, y) e^{ψ(y)}`, for **bounded** `ψ`:
`∑_z K^ψ_s(z, y)² ≤ C₃ s^{−1/β} e^{2δs + 72 Λ(ψ)² s}`, `δ = 4/φ(R)`. This is what the proof of CKS
Theorem 3.25 establishes ((3.9)–(3.24): the `L^{2p}` form inequality and the Nash iteration); CKS's
constants are smaller (`e^{2δs + Λ(ψ)² s}`).

`heatKernel_le_exp_davies_of_core`: `CoreL2 → H5`, by
* clamping (`daviesSq_clamp_le`): `ψₙ = max(−n, min(ψ, n))` has `Λ(ψₙ)² ≤ Λ(ψ)²` and agrees with `ψ`
  at `x, y` once `n ≥ |ψ(x)|, |ψ(y)|` (QUOTES §H5.4 step 1);
* the semigroup law at `t/2`, Cauchy–Schwarz, `p` symmetric and `Λ(−ψ)² = Λ(ψ)²`:
  `K^ψ_t(x, y) ≤ ‖K^{−ψ}_{t/2}(·, x)‖₂ ‖K^ψ_{t/2}(·, y)‖₂`.
-/


open DurrettProbability MarkovChain MarkovHK
open scoped ENNReal

namespace CarlenKusuokaStroock

/-- The core estimate, for bounded `ψ` (the residue of H5). -/
def CoreL2 : Prop :=
  ∀ (C β : ℝ), 0 < C → 0 < β → ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (X : Type u) [Countable X] [DecidableEq X]
    (J ρ : X → X → ℝ) (φ : ℝ → ℝ) (R : ℝ),
    IsTransition J → IsSymmetric J → IsMetric ρ → 0 < φ R →
    SatisfiesNash (nearPart J ρ R) C (4 / φ R) β →
    ∀ ψ : X → ℝ, (∃ M, ∀ z, |ψ z| ≤ M) → daviesSq (nearPart J ρ R) ψ ≠ ⊤ →
    ∀ s : ℝ, 0 < s → ∀ y : X,
      ∑' z, (Real.exp (-ψ z) * heatKernel (nearPart J ρ R) s z y * Real.exp (ψ y)) ^ 2 ≤
        C₃ * s ^ (-1 / β) *
          Real.exp (2 * (4 / φ R) * s + 72 * (daviesSq (nearPart J ρ R) ψ).toReal * s)

namespace H5

variable {X : Type*}

/-- `Λ(−ψ)² = Λ(ψ)²`. -/
lemma daviesSq_neg (K : X → X → ℝ) (ψ : X → ℝ) : daviesSq K (fun z => -ψ z) = daviesSq K ψ := by
  unfold daviesSq
  simp only [neg_neg, mul_neg, neg_mul]
  rw [max_comm]

/-- The per-point form of a half of `Λ(ψ)²`. -/
lemma davies_term (K : X → X → ℝ) (g : X → ℝ) (z : X) :
    ENNReal.ofReal (Real.exp (-2 * g z)) * carreDuChamp K (fun w => Real.exp (g w)) z =
      ∑' w, ENNReal.ofReal ((Real.exp (g w - g z) - 1) ^ 2 * K z w) := by
  unfold carreDuChamp
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun w => ?_
  rcases le_total 0 (K z w) with hK | hK
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    have e1 : Real.exp (-2 * g z) = Real.exp (-g z) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have e2 : Real.exp (g w - g z) = Real.exp (g w) * Real.exp (-g z) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (g z) * Real.exp (-g z) = 1 := by rw [← Real.exp_add]; simp
    rw [e1, e2]
    linear_combination K z w * (Real.exp (g z) * Real.exp (-g z) + 1 -
      2 * Real.exp (g w) * Real.exp (-g z)) * e3
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hK),
      ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hK), mul_zero]

/-- `(e^{s'} − 1)² ≤ (eˢ − 1)²` when `s'` lies between `0` and `s`. -/
lemma exp_sub_one_sq_mono {s s' : ℝ} (h : (0 ≤ s' ∧ s' ≤ s) ∨ (s ≤ s' ∧ s' ≤ 0)) :
    (Real.exp s' - 1) ^ 2 ≤ (Real.exp s - 1) ^ 2 := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have a : 0 ≤ Real.exp s' - 1 := by linarith [Real.one_le_exp h0]
    have b : Real.exp s' ≤ Real.exp s := Real.exp_le_exp.mpr h1
    nlinarith
  · have a : Real.exp s' - 1 ≤ 0 := by linarith [Real.exp_le_one_iff.mpr h1]
    have b : Real.exp s ≤ Real.exp s' := Real.exp_le_exp.mpr h0
    nlinarith [Real.exp_pos s]

/-- Clamping. -/
noncomputable def clamp (n : ℝ) (ψ : X → ℝ) : X → ℝ := fun z => max (-n) (min (ψ z) n)

lemma clampR {n a b : ℝ} (h : a ≤ b) :
    0 ≤ max (-n) (min b n) - max (-n) (min a n) ∧
      max (-n) (min b n) - max (-n) (min a n) ≤ b - a := by
  constructor
  · have : min a n ≤ min b n := min_le_min_right n h
    have := max_le_max (le_refl (-n)) this
    linarith
  · have h1 := abs_max_sub_max_le_abs (min b n) (min a n) (-n)
    have h2 := abs_min_sub_min_le_max b n a n
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), abs_of_nonneg (by linarith : 0 ≤ b - a)]
      at h2
    rw [max_comm (min b n), max_comm (min a n)] at h1
    have h3 := le_abs_self (max (-n) (min b n) - max (-n) (min a n))
    linarith

lemma clamp_between (n : ℝ) (ψ : X → ℝ) (z w : X) :
    (0 ≤ clamp n ψ w - clamp n ψ z ∧ clamp n ψ w - clamp n ψ z ≤ ψ w - ψ z) ∨
      (ψ w - ψ z ≤ clamp n ψ w - clamp n ψ z ∧ clamp n ψ w - clamp n ψ z ≤ 0) := by
  unfold clamp
  rcases le_total (ψ z) (ψ w) with h | h
  · left; exact clampR h
  · right
    obtain ⟨h1, h2⟩ := clampR (n := n) h
    constructor <;> linarith

/-- Clamping does not increase `Λ(ψ)²`. -/
lemma daviesSq_clamp_le {K : X → X → ℝ} (hK : ∀ z w, 0 ≤ K z w) (n : ℝ) (ψ : X → ℝ) :
    daviesSq K (clamp n ψ) ≤ daviesSq K ψ := by
  unfold daviesSq
  refine max_le_max (iSup_mono fun z => ?_) (iSup_mono fun z => ?_)
  · rw [davies_term, davies_term]
    refine ENNReal.tsum_le_tsum fun w => ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (exp_sub_one_sq_mono (clamp_between n ψ z w)) (hK z w)
  · have e : ∀ g : X → ℝ, ENNReal.ofReal (Real.exp (2 * g z)) *
        carreDuChamp K (fun y => Real.exp (-g y)) z =
        ∑' w, ENNReal.ofReal ((Real.exp (-g w - -g z) - 1) ^ 2 * K z w) := by
      intro g
      have := davies_term K (fun y => -g y) z
      rw [show (2 : ℝ) * g z = -2 * -g z by ring]; exact this
    rw [e, e]
    refine ENNReal.tsum_le_tsum fun w => ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_right (exp_sub_one_sq_mono ?_) (hK z w)
    rcases clamp_between n ψ z w with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; constructor <;> linarith
    · left; constructor <;> linarith

/-- Cauchy–Schwarz for series. -/
lemma sq_tsum_mul_le' {u v : X → ℝ} (hu : Summable (fun z => u z ^ 2))
    (hv : Summable (fun z => v z ^ 2)) (huv : Summable (fun z => u z * v z)) :
    (∑' z, u z * v z) ^ 2 ≤ (∑' z, u z ^ 2) * ∑' z, v z ^ 2 := by
  set A := ∑' z, u z ^ 2
  set B := ∑' z, u z * v z
  set C := ∑' z, v z ^ 2
  have hq : ∀ l : ℝ, 0 ≤ A - 2 * l * B + l ^ 2 * C := by
    intro l
    have e : ∀ z, (u z - l * v z) ^ 2 = u z ^ 2 - 2 * l * (u z * v z) + l ^ 2 * v z ^ 2 :=
      fun z => by ring
    have h0 : 0 ≤ ∑' z, (u z - l * v z) ^ 2 := tsum_nonneg fun z => sq_nonneg _
    simp only [e] at h0
    rwa [(hu.sub (huv.mul_left (2 * l))).tsum_add (hv.mul_left (l ^ 2)),
      hu.tsum_sub (huv.mul_left (2 * l)), tsum_mul_left, tsum_mul_left] at h0
  have hC0 : 0 ≤ C := tsum_nonneg fun z => sq_nonneg _
  rcases hC0.lt_or_eq with hCpos | hCz
  · have := hq (B / C)
    have e : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hCpos] at this
    linarith
  · rw [← hCz, mul_zero]
    by_contra hcon
    push_neg at hcon
    have hB : B ≠ 0 := by intro h; rw [h] at hcon; simp at hcon
    have h1 := hq ((A + 1) / B)
    rw [← hCz] at h1
    have e : A - 2 * ((A + 1) / B) * B + ((A + 1) / B) ^ 2 * 0 = A - 2 * (A + 1) := by
      field_simp; ring
    rw [e] at h1
    have hA0 : 0 ≤ A := tsum_nonneg fun z => sq_nonneg _
    linarith

end H5

open H5 in
/-- **H5 from the core estimate.** -/
theorem heatKernel_le_exp_davies_of_core (hcore : CoreL2.{u}) (C β : ℝ) (hC : 0 < C)
    (hβ : 0 < β) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J ρ : X → X → ℝ)
      (φ : ℝ → ℝ) (R : ℝ),
      IsTransition J → IsSymmetric J → IsMetric ρ → 0 < φ R →
      SatisfiesNash (nearPart J ρ R) C (4 / φ R) β →
      ∀ ψ : X → ℝ, daviesSq (nearPart J ρ R) ψ ≠ ⊤ → ∀ t : ℝ, 0 < t → ∀ x y,
        heatKernel (nearPart J ρ R) t x y ≤
          C₂ * t ^ (-1 / β) *
            Real.exp (4 * t / φ R + 72 * (daviesSq (nearPart J ρ R) ψ).toReal * t - ψ y + ψ x) := by
  obtain ⟨C₃, hC₃, hcore'⟩ := hcore C β hC hβ
  refine ⟨C₃ * 2 ^ (1 / β), by positivity, ?_⟩
  intro X _ _ J ρ φ R hJ hJs hρ hφR hN ψ hψ t ht x y
  set K := nearPart J ρ R with hKdef
  have hK0 : ∀ z w, 0 ≤ K z w := nearPart_nonneg hJ R
  set U := uniformize K with hU
  have hUT : IsTransition U := isTransition_uniformize (nearPart_nonneg hJ R)
    (summable_nearPart hJ R) (tsum_nearPart_le hJ R)
  have hUs : IsSymmetric U := uniformize_symm (nearPart_symm hJs hρ R)
  have hpRU : ∀ s u v, heatKernel K s u v = heatKernel U s u v := by
    intro s u v; rw [heatKernel_eq, heatKernel_eq, uniformize_eq_self hUT]
  -- clamp
  set n := max |ψ x| |ψ y| with hn
  have hn0 : 0 ≤ n := le_trans (abs_nonneg _) (le_max_left _ _)
  set ψ' := clamp n ψ with hψ'
  have hcl : ∀ z, |ψ z| ≤ n → ψ' z = ψ z := by
    intro z hz
    simp only [hψ', clamp]
    rw [min_eq_left (le_of_abs_le hz), max_eq_right (neg_le_of_abs_le hz)]
  have hψ'x : ψ' x = ψ x := hcl x (le_max_left _ _)
  have hψ'y : ψ' y = ψ y := hcl y (le_max_right _ _)
  have hψ'b : ∀ z, |ψ' z| ≤ n := by
    intro z; simp only [hψ', clamp]
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_right _ _)
  have hD' := daviesSq_clamp_le hK0 n ψ
  rw [← hψ'] at hD'
  have hD'ne : daviesSq K ψ' ≠ ⊤ := ne_top_of_le_ne_top hψ hD'
  have hDr : (daviesSq K ψ').toReal ≤ (daviesSq K ψ).toReal := ENNReal.toReal_mono hψ hD'
  have hDn : daviesSq K (fun z => -ψ' z) = daviesSq K ψ' := daviesSq_neg K ψ'
  have hD'0 : 0 ≤ (daviesSq K ψ').toReal := ENNReal.toReal_nonneg
  -- the core estimate at `s = t/2`, for `ψ'` (column `y`) and `−ψ'` (column `x`)
  set s := t / 2 with hs
  have hs0 : 0 < s := by positivity
  have hA := hcore' X J ρ φ R hJ hJs hρ hφR hN ψ' ⟨n, hψ'b⟩ hD'ne s hs0 y
  have hB := hcore' X J ρ φ R hJ hJs hρ hφR hN (fun z => -ψ' z)
    ⟨n, fun z => by rw [abs_neg]; exact hψ'b z⟩ (by rw [hDn]; exact hD'ne) s hs0 x
  rw [hDn] at hB
  set M := C₃ * s ^ (-1 / β) * Real.exp (2 * (4 / φ R) * s + 72 * (daviesSq K ψ').toReal * s)
    with hM
  have hM0 : 0 ≤ M := by positivity
  -- the semigroup and Cauchy–Schwarz
  set a : X → ℝ := fun z => Real.exp (-(-ψ' z)) * heatKernel K s z x * Real.exp (-ψ' x) with ha
  set b : X → ℝ := fun z => Real.exp (-ψ' z) * heatKernel K s z y * Real.exp (ψ' y) with hb
  have hen : ∀ z, Real.exp (ψ' z) ≤ Real.exp n ∧ Real.exp (-ψ' z) ≤ Real.exp n := fun z =>
    ⟨Real.exp_le_exp.mpr (le_of_abs_le (hψ'b z)),
      Real.exp_le_exp.mpr (by have := neg_abs_le (ψ' z); linarith [hψ'b z])⟩
  have hcol : ∀ v, Summable (fun z => heatKernel K s z v) := fun v => by
    simp only [hpRU]
    exact (summable_heat_row hUT hs0.le v).congr fun z => heat_symm hUT hUs s v z
  have hsq : ∀ (c : X → ℝ) (v : X), (∀ z, |c z| ≤ Real.exp n * Real.exp n *
      heatKernel K s z v) → Summable (fun z => c z ^ 2) := by
    intro c v hc
    refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
      ((hcol v).mul_left ((Real.exp n * Real.exp n) ^ 2))
    have h1 := hc z
    have h2 : heatKernel K s z v ≤ 1 := by rw [hpRU]; exact heat_le_one hUT hs0.le z v
    have h3 : 0 ≤ heatKernel K s z v := by rw [hpRU]; exact heat_nonneg hUT hs0.le z v
    rw [← sq_abs]
    calc |c z| ^ 2 ≤ (Real.exp n * Real.exp n * heatKernel K s z v) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (Real.exp n * Real.exp n) ^ 2 * (heatKernel K s z v * heatKernel K s z v) := by ring
      _ ≤ (Real.exp n * Real.exp n) ^ 2 * heatKernel K s z v := by
          gcongr; nlinarith
  have hpos : ∀ z v, 0 ≤ heatKernel K s z v := fun z v => by
    rw [hpRU]; exact heat_nonneg hUT hs0.le z v
  have ha2 : Summable (fun z => a z ^ 2) := hsq a x fun z => by
    simp only [ha]
    rw [abs_of_nonneg (by have := hpos z x; positivity)]
    have := hen z; have := hen x
    calc Real.exp (-(-ψ' z)) * heatKernel K s z x * Real.exp (-ψ' x)
        = Real.exp (ψ' z) * Real.exp (-ψ' x) * heatKernel K s z x := by rw [neg_neg]; ring
      _ ≤ Real.exp n * Real.exp n * heatKernel K s z x :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hen z).1 (hen x).2 (Real.exp_pos _).le
            (Real.exp_pos _).le) (hpos z x)
  have hb2 : Summable (fun z => b z ^ 2) := hsq b y fun z => by
    simp only [hb]
    rw [abs_of_nonneg (by have := hpos z y; positivity)]
    have := hen z; have := hen y
    calc Real.exp (-ψ' z) * heatKernel K s z y * Real.exp (ψ' y)
        = Real.exp (-ψ' z) * Real.exp (ψ' y) * heatKernel K s z y := by ring
      _ ≤ Real.exp n * Real.exp n * heatKernel K s z y :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hen z).2 (hen y).1 (Real.exp_pos _).le
            (Real.exp_pos _).le) (hpos z y)
  have hab : Summable (fun z => a z * b z) :=
    Summable.of_nonneg_of_le (fun z => by
      simp only [ha, hb]; have := hpos z x; have := hpos z y; positivity)
      (fun z => by nlinarith [sq_nonneg (a z - b z)]) ((ha2.add hb2).div_const 2)
  -- the kernel at time `t`
  have hsg : heatKernel K t x y = ∑' z, heatKernel K s x z * heatKernel K s z y := by
    simp only [hpRU]
    rw [heat_semigroup hUT hs0.le hs0.le, show s + s = t by rw [hs]; ring]
  have hKt : Real.exp (-ψ' x) * heatKernel K t x y * Real.exp (ψ' y) = ∑' z, a z * b z := by
    rw [hsg, ← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr fun z => ?_
    simp only [ha, hb]
    rw [show heatKernel K s x z = heatKernel K s z x by
      rw [hpRU, hpRU]; exact heat_symm hUT hUs s x z, neg_neg]
    have e : Real.exp (ψ' z) * Real.exp (-ψ' z) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-(Real.exp (-ψ' x) * heatKernel K s z x * heatKernel K s z y *
      Real.exp (ψ' y))) * e
  have hCS := sq_tsum_mul_le' ha2 hb2 hab
  have hA' : ∑' z, a z ^ 2 ≤ M := by
    simp only [ha]; exact hB
  have hB' : ∑' z, b z ^ 2 ≤ M := hA
  have hKle : Real.exp (-ψ' x) * heatKernel K t x y * Real.exp (ψ' y) ≤ M := by
    rw [hKt]
    have h0 : 0 ≤ ∑' z, a z * b z :=
      tsum_nonneg fun z => by simp only [ha, hb]; have := hpos z x; have := hpos z y; positivity
    have h1 : (∑' z, a z * b z) ^ 2 ≤ M ^ 2 := by
      calc (∑' z, a z * b z) ^ 2 ≤ (∑' z, a z ^ 2) * ∑' z, b z ^ 2 := hCS
        _ ≤ M * M := mul_le_mul hA' hB' (tsum_nonneg fun z => sq_nonneg _) hM0
        _ = M ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ h0 hM0 (by norm_num)).mp h1
  -- unwind
  have hptxy : heatKernel K t x y =
      (Real.exp (-ψ' x) * heatKernel K t x y * Real.exp (ψ' y)) *
        Real.exp (ψ' x - ψ' y) := by
    rw [show ψ' x - ψ' y = ψ' x + -ψ' y by ring, Real.exp_add]
    have e1 : Real.exp (-ψ' x) * Real.exp (ψ' x) = 1 := by rw [← Real.exp_add]; simp
    have e2 : Real.exp (ψ' y) * Real.exp (-ψ' y) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-(heatKernel K t x y) * Real.exp (ψ' y) * Real.exp (-ψ' y)) * e1 -
      heatKernel K t x y * e2
  rw [hptxy, hψ'x, hψ'y]
  rw [hψ'x, hψ'y] at hKle
  have hsb : s ^ (-1 / β) = 2 ^ (1 / β) * t ^ (-1 / β) := by
    rw [hs, Real.div_rpow ht.le (by norm_num), neg_div, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  calc Real.exp (-ψ x) * heatKernel K t x y * Real.exp (ψ y) * Real.exp (ψ x - ψ y)
      ≤ M * Real.exp (ψ x - ψ y) := mul_le_mul_of_nonneg_right hKle (Real.exp_pos _).le
    _ = C₃ * 2 ^ (1 / β) * t ^ (-1 / β) *
          Real.exp (4 * t / φ R + 36 * (daviesSq K ψ').toReal * t - ψ y + ψ x) := by
        rw [hM, hsb, mul_assoc, ← Real.exp_add]
        rw [show 2 * (4 / φ R) * s + 72 * (daviesSq K ψ').toReal * s + (ψ x - ψ y) =
          4 * t / φ R + 36 * (daviesSq K ψ').toReal * t - ψ y + ψ x by rw [hs]; ring]
        ring
    _ ≤ C₃ * 2 ^ (1 / β) * t ^ (-1 / β) *
          Real.exp (4 * t / φ R + 72 * (daviesSq K ψ).toReal * t - ψ y + ψ x) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have : 36 * (daviesSq K ψ').toReal * t ≤ 72 * (daviesSq K ψ).toReal * t := by
          nlinarith
        linarith


end CarlenKusuokaStroock
end

section
/-!
# H5 core, step 2: the two scalar differential inequalities

* `gronwall_le`: if `u' ≤ λu` on `(a, b)` (`u` continuous on `[a, b]`), then
  `u(b) ≤ e^{λ(b − a)} u(a)`;
* `nash_ode`: if `G ≥ 0` and `G' ≤ −κ G^{1+β}` on `(a, b)`, then `G(b) ≤ (βκ(b − a))^{−1/β}`;
* `nash_ode_exp`: if `u ≥ 0` and `u' ≤ −κ u^{1+β} + λu` on `(a, b)` with `λ ≥ 0`, then
  `u(b) ≤ e^{λ(b − a)} (βκ(b − a))^{−1/β}` (CKS Lemma (3.21), in the form used on each window
  of the iteration).
-/

open Set

namespace MarkovHK.H5Core

/-- Grönwall. -/
lemma gronwall_le {u u' : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hc : ContinuousOn u (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt u (u' s) s) (hle : ∀ s ∈ Ioo a b, u' s ≤ lam * u s) :
    u b ≤ Real.exp (lam * (b - a)) * u a := by
  set G : ℝ → ℝ := fun s => Real.exp (-lam * s) * u s with hG
  have hGc : ContinuousOn G (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc
  have hGd : ∀ s ∈ Ioo a b, HasDerivAt G (Real.exp (-lam * s) * (u' s - lam * u s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => Real.exp (-lam * s)) (Real.exp (-lam * s) * -lam) s := by
      have := ((hasDerivAt_id s).const_mul (-lam)).exp
      simpa using this
    exact (h1.mul (hd s hs)).congr_deriv (by ring)
  have hanti : AntitoneOn G (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hGc ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      exact (hGd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hGd s hs).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hle s hs])
  have h := hanti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  simp only [hG] at h
  have e : u b = Real.exp (lam * b) * (Real.exp (-lam * b) * u b) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [e]
  calc Real.exp (lam * b) * (Real.exp (-lam * b) * u b)
      ≤ Real.exp (lam * b) * (Real.exp (-lam * a) * u a) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (lam * (b - a)) * u a := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-- The Nash ODE. -/
lemma nash_ode {G G' : ℝ → ℝ} {a b κ β : ℝ} (hab : a < b) (hκ : 0 < κ) (hβ : 0 < β)
    (hc : ContinuousOn G (Icc a b)) (h0 : ∀ s ∈ Icc a b, 0 ≤ G s)
    (hd : ∀ s ∈ Ioo a b, HasDerivAt G (G' s) s)
    (hle : ∀ s ∈ Ioo a b, G' s ≤ -κ * G s ^ (1 + β)) :
    G b ≤ (β * κ * (b - a)) ^ (-1 / β) := by
  have hbm : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have ham : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hpos : 0 < β * κ * (b - a) := by have : 0 < b - a := by linarith
                                        positivity
  rcases (h0 b hbm).eq_or_lt with hz | hGb
  · rw [← hz]; positivity
  -- `G` is antitone, hence positive on `[a, b]`
  have hanti : AntitoneOn G (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hc ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s hs).deriv]
      have := hle s hs
      have : 0 ≤ G s ^ (1 + β) := Real.rpow_nonneg (h0 s (Ioo_subset_Icc_self hs)) _
      nlinarith
  have hGpos : ∀ s ∈ Icc a b, 0 < G s := fun s hs => lt_of_lt_of_le hGb (hanti hs hbm hs.2)
  -- `H = G^{−β} − βκ s` is monotone
  set H : ℝ → ℝ := fun s => G s ^ (-β) - β * κ * s with hH
  have hHd : ∀ s ∈ Ioo a b, HasDerivAt H ((-β) * G s ^ (-β - 1) * G' s - β * κ) s := by
    intro s hs
    have h1 := (hd s hs).rpow_const (p := -β) (Or.inl (hGpos s (Ioo_subset_Icc_self hs)).ne')
    have h2 := (hasDerivAt_id s).const_mul (β * κ)
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono : MonotoneOn H (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ((continuous_const.mul continuous_id).continuousOn)
      exact hc.rpow_const (fun s hs => Or.inl (hGpos s hs).ne')
    · intro s hs
      rw [interior_Icc] at hs
      exact (hHd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hHd s hs).deriv]
      have hGs := hGpos s (Ioo_subset_Icc_self hs)
      have hprod : G s ^ (-β - 1) * G s ^ (1 + β) = 1 := by
        rw [← Real.rpow_add hGs, show -β - 1 + (1 + β) = 0 by ring, Real.rpow_zero]
      have hp : 0 ≤ G s ^ (-β - 1) := (Real.rpow_pos_of_pos hGs _).le
      have hle' := mul_le_mul_of_nonneg_left (hle s hs) hp
      have : (-β) * G s ^ (-β - 1) * G' s ≥ β * κ := by
        have e : G s ^ (-β - 1) * (-κ * G s ^ (1 + β)) = -κ := by
          rw [show G s ^ (-β - 1) * (-κ * G s ^ (1 + β)) =
            -κ * (G s ^ (-β - 1) * G s ^ (1 + β)) by ring, hprod, mul_one]
        rw [e] at hle'
        nlinarith
      linarith
  have hHab := hmono ham hbm hab.le
  simp only [hH] at hHab
  have hGa : 0 ≤ G a ^ (-β) := (Real.rpow_pos_of_pos (hGpos a ham) _).le
  have hkey : β * κ * (b - a) ≤ G b ^ (-β) := by nlinarith
  -- invert
  have := Real.rpow_le_rpow_of_nonpos hpos hkey (show -1 / β ≤ 0 by
    rw [neg_div]; exact neg_nonpos.mpr (by positivity))
  rw [← Real.rpow_mul hGb.le, show -β * (-1 / β) = 1 by field_simp, Real.rpow_one] at this
  exact this

/-- CKS Lemma (3.21), window form. -/
lemma nash_ode_exp {u u' : ℝ → ℝ} {a b κ β lam : ℝ} (hab : a < b) (hκ : 0 < κ) (hβ : 0 < β)
    (hlam : 0 ≤ lam) (hc : ContinuousOn u (Icc a b)) (h0 : ∀ s ∈ Icc a b, 0 ≤ u s)
    (hd : ∀ s ∈ Ioo a b, HasDerivAt u (u' s) s)
    (hle : ∀ s ∈ Ioo a b, u' s ≤ -κ * u s ^ (1 + β) + lam * u s) :
    u b ≤ Real.exp (lam * (b - a)) * (β * κ * (b - a)) ^ (-1 / β) := by
  set G : ℝ → ℝ := fun s => Real.exp (-lam * (s - a)) * u s with hG
  have hGc : ContinuousOn G (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul hc
  have hGd : ∀ s ∈ Ioo a b,
      HasDerivAt G (Real.exp (-lam * (s - a)) * (u' s - lam * u s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => Real.exp (-lam * (s - a)))
        (Real.exp (-lam * (s - a)) * -lam) s := by
      have := (((hasDerivAt_id s).sub_const a).const_mul (-lam)).exp
      simpa using this
    exact (h1.mul (hd s hs)).congr_deriv (by ring)
  have hG0 : ∀ s ∈ Icc a b, 0 ≤ G s := fun s hs => mul_nonneg (Real.exp_pos _).le (h0 s hs)
  have hGle : ∀ s ∈ Ioo a b,
      Real.exp (-lam * (s - a)) * (u' s - lam * u s) ≤ -κ * G s ^ (1 + β) := by
    intro s hs
    have hus := h0 s (Ioo_subset_Icc_self hs)
    set E := Real.exp (-lam * (s - a)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hE1 : E ≤ 1 := by
      rw [hE, Real.exp_le_one_iff]
      have : 0 ≤ s - a := by linarith [hs.1]
      nlinarith
    have h1 : E * (u' s - lam * u s) ≤ E * (-κ * u s ^ (1 + β)) :=
      mul_le_mul_of_nonneg_left (by linarith [hle s hs]) hE0.le
    have h2 : G s ^ (1 + β) = E ^ (1 + β) * u s ^ (1 + β) := by
      simp only [hG]; rw [← hE, Real.mul_rpow hE0.le hus]
    have h3 : E ^ (1 + β) ≤ E := by
      have := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (show (1 : ℝ) ≤ 1 + β by linarith)
      rwa [Real.rpow_one] at this
    have hu1 : 0 ≤ u s ^ (1 + β) := Real.rpow_nonneg hus _
    rw [h2]
    have : E ^ (1 + β) * u s ^ (1 + β) ≤ E * u s ^ (1 + β) := mul_le_mul_of_nonneg_right h3 hu1
    nlinarith
  have := nash_ode hab hκ hβ hGc hG0 hGd hGle
  simp only [hG] at this
  have e : u b = Real.exp (lam * (b - a)) * (Real.exp (-lam * (b - a)) * u b) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [e]
  exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

end MarkovHK.H5Core
end

section
/-!
# H5 core, step 1: the pointwise inequalities behind the `L^{2m}` form inequality

For `a, b ≥ 0`, `E > 0` and `m ≥ 1` (`q = 2m`):
* `sv_ineq` (discrete Stroock–Varopoulos, CKS (3.17) with a weaker constant):
  `(a^m − b^m)² ≤ m (a − b)(a^{2m−1} − b^{2m−1})`;
* `point_ineq`: `a^{2m−1}(E b − a) + b^{2m−1}(a/E − b)
     ≤ −(1/(2m))(a^m − b^m)² + m((E − 1)² + (1/E − 1)²)(a^{2m} + b^{2m})`.
Summed against a symmetric kernel with `E = e^{ψ(w) − ψ(z)}`, the left side is the symmetrised
`⟨L^ψ g, g^{2m−1}⟩` and the right side gives `−(1/2m) ℰ(g^m) + 2mΛ(ψ)²‖g‖_{2m}^{2m}`.
-/

open Finset

namespace MarkovHK.H5Core

/-- Discrete Stroock–Varopoulos. -/
lemma sv_ineq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    (a ^ m - b ^ m) ^ 2 ≤ m * ((a - b) * (a ^ (2 * m - 1) - b ^ (2 * m - 1))) := by
  have h1 := geom_sum₂_mul a b m
  have h2 := geom_sum₂_mul a b (2 * m - 1)
  set G := ∑ i ∈ range m, a ^ i * b ^ (m - 1 - i) with hG
  set H := ∑ i ∈ range (2 * m - 1), a ^ i * b ^ (2 * m - 1 - 1 - i) with hH
  have hCS : G ^ 2 ≤ (m : ℝ) * ∑ i ∈ range m, (a ^ i * b ^ (m - 1 - i)) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range m) (f := fun i => a ^ i * b ^ (m - 1 - i))
    simpa using this
  have hsub : ∑ i ∈ range m, (a ^ i * b ^ (m - 1 - i)) ^ 2 ≤ H := by
    have e : ∀ i ∈ range m, (a ^ i * b ^ (m - 1 - i)) ^ 2 =
        (fun j => a ^ j * b ^ (2 * m - 1 - 1 - j)) (2 * i) := by
      intro i hi
      simp only [mem_range] at hi
      simp only
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 2
      · ring
      · omega
    rw [sum_congr rfl e]
    calc ∑ i ∈ range m, (fun j => a ^ j * b ^ (2 * m - 1 - 1 - j)) (2 * i)
        = ∑ j ∈ (range m).image (fun i => 2 * i), a ^ j * b ^ (2 * m - 1 - 1 - j) :=
          by rw [sum_image (fun x _ y _ h => by omega)]
      _ ≤ H := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
          intro j hj
          simp only [mem_image, mem_range] at hj ⊢
          omega
  have hab2 : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  calc (a ^ m - b ^ m) ^ 2 = (a - b) ^ 2 * G ^ 2 := by rw [← h1]; ring
    _ ≤ (a - b) ^ 2 * ((m : ℝ) * H) :=
        mul_le_mul_of_nonneg_left (hCS.trans (mul_le_mul_of_nonneg_left hsub (by positivity)))
          hab2
    _ = m * ((a - b) * (a ^ (2 * m - 1) - b ^ (2 * m - 1))) := by rw [← h2]; ring

/-- For `a ≥ b ≥ 0`: `0 ≤ a^{2n+1} b − a b^{2n+1} ≤ a^{2n+2} − b^{2n+2}`. -/
lemma cross_le_of_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (n : ℕ) :
    0 ≤ a ^ (2 * n + 1) * b - a * b ^ (2 * n + 1) ∧
      a ^ (2 * n + 1) * b - a * b ^ (2 * n + 1) ≤ a ^ (2 * n + 2) - b ^ (2 * n + 2) := by
  have ha : 0 ≤ a := hb.trans hab
  have p1 : b ^ (2 * n) ≤ a ^ (2 * n) := pow_le_pow_left₀ hb hab _
  have p2 : b ^ (2 * n + 1) ≤ a ^ (2 * n + 1) := pow_le_pow_left₀ hb hab _
  have e1 : a ^ (2 * n + 1) * b - a * b ^ (2 * n + 1) = a * b * (a ^ (2 * n) - b ^ (2 * n)) := by
    ring
  have e2 : a ^ (2 * n + 2) - b ^ (2 * n + 2) - (a ^ (2 * n + 1) * b - a * b ^ (2 * n + 1)) =
      (a - b) * (a ^ (2 * n + 1) + b ^ (2 * n + 1)) := by ring
  constructor
  · rw [e1]; exact mul_nonneg (mul_nonneg ha hb) (by linarith)
  · have : 0 ≤ (a - b) * (a ^ (2 * n + 1) + b ^ (2 * n + 1)) :=
      mul_nonneg (by linarith) (by positivity)
    linarith

/-- `|a^{2n+1} b − a b^{2n+1}| ≤ |a^{n+1} − b^{n+1}| (a^{n+1} + b^{n+1})`. -/
lemma abs_cross_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    |a ^ (2 * n + 1) * b - a * b ^ (2 * n + 1)| ≤
      |a ^ (n + 1) - b ^ (n + 1)| * (a ^ (n + 1) + b ^ (n + 1)) := by
  have sq : ∀ x : ℝ, x ^ (2 * n + 2) = (x ^ (n + 1)) ^ 2 := fun x => by rw [← pow_mul]; ring_nf
  rcases le_total b a with hab | hab
  · obtain ⟨h0, h1⟩ := cross_le_of_le hb hab n
    have hp : b ^ (n + 1) ≤ a ^ (n + 1) := pow_le_pow_left₀ hb hab _
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    rw [sq, sq] at h1
    nlinarith
  · obtain ⟨h0, h1⟩ := cross_le_of_le ha hab n
    have hp : a ^ (n + 1) ≤ b ^ (n + 1) := pow_le_pow_left₀ ha hab _
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    rw [sq, sq] at h1
    nlinarith

/-- `(a − b)(a^{2n+1} − b^{2n+1}) ≥ 0`. -/
lemma mono_prod_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ (a - b) * (a ^ (2 * n + 1) - b ^ (2 * n + 1)) := by
  rcases le_total b a with hab | hab
  · exact mul_nonneg (by linarith) (by linarith [pow_le_pow_left₀ hb hab (2 * n + 1)])
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith [pow_le_pow_left₀ ha hab (2 * n + 1)])

/-- The pointwise inequality, with `m = n + 1`. -/
lemma point_ineq {a b E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hE : 0 < E) (n : ℕ) :
    a ^ (2 * n + 1) * (E * b - a) + b ^ (2 * n + 1) * (a / E - b) ≤
      -(1 / (2 * (n + 1 : ℝ))) * (a ^ (n + 1) - b ^ (n + 1)) ^ 2 +
        (n + 1 : ℝ) * ((E - 1) ^ 2 + (1 / E - 1) ^ 2) * (a ^ (2 * n + 2) + b ^ (2 * n + 2)) := by
  set m : ℝ := n + 1 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hm0 : 0 < m := by linarith
  set A := a ^ (n + 1) with hA
  set B := b ^ (n + 1) with hB
  set P := a ^ (2 * n + 1) with hP
  set Q := b ^ (2 * n + 1) with hQ
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hAA : a ^ (2 * n + 2) = A ^ 2 := by rw [hA, ← pow_mul]; ring_nf
  have hBB : b ^ (2 * n + 2) = B ^ 2 := by rw [hB, ← pow_mul]; ring_nf
  have haP : a * P = A ^ 2 := by rw [← hAA, hP]; ring
  have hbQ : b * Q = B ^ 2 := by rw [← hBB, hQ]; ring
  rw [hAA, hBB]
  -- Stroock–Varopoulos
  have hsv : (A - B) ^ 2 ≤ m * ((a - b) * (P - Q)) := by
    have := sv_ineq ha hb (n + 1)
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega] at this
    push_cast at this
    exact this
  have hmono := mono_prod_nonneg ha hb n
  rw [← hP, ← hQ] at hmono
  -- the cross term
  have hcross : |P * b - a * Q| ≤ |A - B| * (A + B) := abs_cross_le ha hb n
  set s := E - 1 with hs
  set s' := 1 / E - 1 with hs'
  have hEinv : E * (1 / E) = 1 := by field_simp
  have hss : s + s' = s ^ 2 * (1 / E) := by
    rw [hs, hs']; field_simp; ring
  have hss0 : 0 ≤ s + s' := by rw [hss]; positivity
  have hss1 : s + s' ≤ (s ^ 2 + s' ^ 2) / 2 := by
    have e : s' = -s * (1 / E) := by rw [hs, hs']; field_simp; ring
    rw [hss, e]
    have : 0 ≤ s ^ 2 * (1 - 1 / E) ^ 2 := by positivity
    have e2 : (s ^ 2 + (-s * (1 / E)) ^ 2) / 2 - s ^ 2 * (1 / E) = s ^ 2 * (1 - 1 / E) ^ 2 / 2 := by
      ring
    linarith
  -- decomposition of the left side
  have hL : P * (E * b - a) + Q * (a / E - b) =
      -((a - b) * (P - Q)) + ((s - s') / 2) * (P * b - a * Q) +
        ((s + s') / 2) * (P * b + a * Q) := by
    rw [hs, hs']
    ring
  rw [hL]
  -- `Pb + aQ ≤ A² + B²`
  have hsym : P * b + a * Q ≤ A ^ 2 + B ^ 2 := by
    have e : (a - b) * (P - Q) = a * P + b * Q - (P * b + a * Q) := by ring
    linarith
  have hsymt : ((s + s') / 2) * (P * b + a * Q) ≤ ((s ^ 2 + s' ^ 2) / 4) * (A ^ 2 + B ^ 2) := by
    have h1 : ((s + s') / 2) * (P * b + a * Q) ≤ ((s + s') / 2) * (A ^ 2 + B ^ 2) :=
      mul_le_mul_of_nonneg_left hsym (by linarith)
    have h2 : ((s + s') / 2) * (A ^ 2 + B ^ 2) ≤ ((s ^ 2 + s' ^ 2) / 4) * (A ^ 2 + B ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  -- the antisymmetric term, by AM-GM
  set x := (s - s') / 2 with hx
  have hxt : x * (P * b - a * Q) ≤ (1 / (2 * m)) * (A - B) ^ 2 + (m / 2) * x ^ 2 * (A + B) ^ 2 := by
    have h1 : x * (P * b - a * Q) ≤ |x| * (|A - B| * (A + B)) := by
      calc x * (P * b - a * Q) ≤ |x * (P * b - a * Q)| := le_abs_self _
        _ = |x| * |P * b - a * Q| := abs_mul _ _
        _ ≤ |x| * (|A - B| * (A + B)) := mul_le_mul_of_nonneg_left hcross (abs_nonneg _)
    have h2 : |x| * (|A - B| * (A + B)) ≤
        (1 / (2 * m)) * (A - B) ^ 2 + (m / 2) * x ^ 2 * (A + B) ^ 2 := by
      have hsq : 0 ≤ (1 / (2 * m)) * (m * |x| * (A + B) - |A - B|) ^ 2 := by positivity
      have e : (1 / (2 * m)) * (m * |x| * (A + B) - |A - B|) ^ 2 =
          (m / 2) * x ^ 2 * (A + B) ^ 2 - |x| * (|A - B| * (A + B)) +
            (1 / (2 * m)) * (A - B) ^ 2 := by
        rw [← sq_abs x, ← sq_abs (A - B)]
        field_simp
        ring
      linarith
    linarith
  have hx2 : x ^ 2 ≤ (s ^ 2 + s' ^ 2) / 2 := by
    have e : (s ^ 2 + s' ^ 2) / 2 - x ^ 2 = (s + s') ^ 2 / 4 := by rw [hx]; ring
    linarith [sq_nonneg (s + s')]
  have hAB2 : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
    have e : 2 * (A ^ 2 + B ^ 2) - (A + B) ^ 2 = (A - B) ^ 2 := by ring
    linarith [sq_nonneg (A - B)]
  have hxt2 : (m / 2) * x ^ 2 * (A + B) ^ 2 ≤ (m / 2) * (s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2) := by
    have h0 : 0 ≤ m / 2 := by positivity
    calc (m / 2) * x ^ 2 * (A + B) ^ 2 ≤ (m / 2) * ((s ^ 2 + s' ^ 2) / 2) * (2 * (A ^ 2 + B ^ 2)) := by
          gcongr
      _ = (m / 2) * (s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2) := by ring
  -- assemble
  have hSV' : -((a - b) * (P - Q)) ≤ -(1 / m) * (A - B) ^ 2 := by
    have : (1 / m) * (A - B) ^ 2 ≤ (a - b) * (P - Q) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm0]; linarith
    linarith
  have hfin : -(1 / m) * (A - B) ^ 2 + (1 / (2 * m)) * (A - B) ^ 2 =
      -(1 / (2 * m)) * (A - B) ^ 2 := by field_simp; ring
  have hcoef : ((s ^ 2 + s' ^ 2) / 4) * (A ^ 2 + B ^ 2) +
      (m / 2) * (s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2) ≤ m * (s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2) := by
    have h0 : 0 ≤ (s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2) := by positivity
    have e : m * (s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2) - (((s ^ 2 + s' ^ 2) / 4) * (A ^ 2 + B ^ 2) +
      (m / 2) * (s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2)) =
        (m / 2 - 1 / 4) * ((s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2)) := by ring
    have : 0 ≤ (m / 2 - 1 / 4) * ((s ^ 2 + s' ^ 2) * (A ^ 2 + B ^ 2)) :=
      mul_nonneg (by linarith) h0
    linarith
  linarith

end MarkovHK.H5Core
end

section
/-!
# H5 core, step 3: the `L^{2m}` form inequality for the twisted generator (CKS (3.10)/(3.11))

For a symmetric transition kernel `U`, a bounded `φ`, and `0 ≤ g ≤ B` summable, with the twisted
generator `(L^φ g)(z) = ∑_w U(z, w)(e^{φ(w) − φ(z)} g(w) − g(z))` and
`∑_w U(z, w)((e^{φ(w)−φ(z)} − 1)² + (e^{φ(z)−φ(w)} − 1)²) ≤ 2Λ₂` for every `z`:

`∑_z g(z)^{2m−1} (L^φ g)(z) ≤ −(1/4m) ∑_{z,w} U(z,w)(g(z)^m − g(w)^m)² + 2mΛ₂ ∑_z g(z)^{2m}`

(`form_ineq`, `m = n + 1`). Proof: symmetrise the double sum and apply `point_ineq`.
-/

open DurrettProbability MarkovChain

namespace MarkovHK.H5Core

variable {X : Type*}

/-- The twisted generator. -/
noncomputable def gen (U : X → X → ℝ) (φ : X → ℝ) (g : X → ℝ) (z : X) : ℝ :=
  ∑' w, U z w * (Real.exp (φ w - φ z) * g w - g z)

/-- The Davies weight `(e^{φ(w)−φ(z)} − 1)² + (e^{φ(z)−φ(w)} − 1)²`. -/
noncomputable def dw (φ : X → ℝ) (z w : X) : ℝ :=
  (Real.exp (φ w - φ z) - 1) ^ 2 + (Real.exp (φ z - φ w) - 1) ^ 2

lemma dw_nonneg (φ : X → ℝ) (z w : X) : 0 ≤ dw φ z w := by unfold dw; positivity

lemma dw_symm (φ : X → ℝ) (z w : X) : dw φ z w = dw φ w z := by unfold dw; ring

lemma exp_diff_le {φ : X → ℝ} {M : ℝ} (hM : ∀ z, |φ z| ≤ M) (z w : X) :
    Real.exp (φ w - φ z) ≤ Real.exp (2 * M) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 := (abs_le.mp (hM z)); have h2 := (abs_le.mp (hM w))
  linarith [h1.1, h2.2]

lemma dw_le {φ : X → ℝ} {M : ℝ} (hM : ∀ z, |φ z| ≤ M) (z w : X) :
    dw φ z w ≤ 2 * (Real.exp (2 * M) + 1) ^ 2 := by
  unfold dw
  have h1 := exp_diff_le hM z w
  have h2 := exp_diff_le hM w z
  have e1 := Real.exp_pos (φ w - φ z)
  have e2 := Real.exp_pos (φ z - φ w)
  have b1 : (Real.exp (φ w - φ z) - 1) ^ 2 ≤ (Real.exp (2 * M) + 1) ^ 2 :=
    sq_le_sq' (by linarith [Real.exp_pos (2 * M)]) (by linarith [Real.exp_pos (2 * M)])
  have b2 : (Real.exp (φ z - φ w) - 1) ^ 2 ≤ (Real.exp (2 * M) + 1) ^ 2 :=
    sq_le_sq' (by linarith [Real.exp_pos (2 * M)]) (by linarith [Real.exp_pos (2 * M)])
  linarith

lemma summable_pair_left {U : X → X → ℝ} (hU : IsSub U) {c : X → ℝ} (hc0 : ∀ z, 0 ≤ c z)
    (hc : Summable c) : Summable (fun p : X × X => U p.1 p.2 * c p.1) := by
  have := summable_triple hc0 hc hU (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
  refine this.congr fun p => ?_
  ring

lemma summable_pair_right {U : X → X → ℝ} (hU : IsSub U) (hUs : IsSymmetric U) {c : X → ℝ}
    (hc0 : ∀ z, 0 ≤ c z) (hc : Summable c) : Summable (fun p : X × X => U p.1 p.2 * c p.2) := by
  have := (summable_pair_left hU hc0 hc).prod_symm
  refine this.congr fun p => ?_
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hUs]

/-- Exchange of the two coordinates in a sum over `X × X`. -/
lemma tsum_swap' (F : X × X → ℝ) : ∑' p : X × X, F p.swap = ∑' p : X × X, F p :=
  (Equiv.prodComm X X).tsum_eq F

lemma pow_le_mul {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (k : ℕ) : x ^ (k + 1) ≤ B ^ k * x := by
  rw [pow_succ]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hxB k) hx0

lemma summable_gpow {g : X → ℝ} (hg0 : ∀ z, 0 ≤ g z) {B : ℝ} (hgB : ∀ z, g z ≤ B)
    (hg : Summable g) (k : ℕ) : Summable (fun z => g z ^ (k + 1)) :=
  Summable.of_nonneg_of_le (fun z => by have := hg0 z; positivity)
    (fun z => pow_le_mul (hg0 z) (hgB z) k) (hg.mul_left (B ^ k))

/-- **The form inequality.** -/
theorem form_ineq {U : X → X → ℝ} (hU : IsTransition U) (hUs : IsSymmetric U) {φ : X → ℝ}
    {M : ℝ} (hM : ∀ z, |φ z| ≤ M) {g : X → ℝ} (hg0 : ∀ z, 0 ≤ g z) {B : ℝ}
    (hgB : ∀ z, g z ≤ B) (hg : Summable g) {Λ2 : ℝ}
    (hΛ : ∀ z, ∑' w, U z w * dw φ z w ≤ 2 * Λ2) (n : ℕ) :
    ∑' z, g z ^ (2 * n + 1) * gen U φ g z ≤
      -(1 / (4 * (n + 1 : ℝ))) * ∑' p : X × X, U p.1 p.2 * (g p.1 ^ (n + 1) - g p.2 ^ (n + 1)) ^ 2
        + 2 * (n + 1 : ℝ) * Λ2 * ∑' z, g z ^ (2 * n + 2) := by
  have hS := isSub_of_isTransition hU
  have hU0 := hU.1
  set m : ℝ := n + 1 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hB0 : ∀ z, 0 ≤ B := fun z => (hg0 z).trans (hgB z)
  set K := Real.exp (2 * M) with hK
  have hK0 : 0 < K := Real.exp_pos _
  -- the summand
  set T : X × X → ℝ := fun p =>
    g p.1 ^ (2 * n + 1) * (U p.1 p.2 * (Real.exp (φ p.2 - φ p.1) * g p.2 - g p.1)) with hT
  have hgq := summable_gpow hg0 hgB hg (2 * n + 1)
  have hgm := summable_gpow hg0 hgB hg n
  have hTs : Summable T := by
    have h1 := summable_pair_right hS hUs hg0 hg
    have h2 := summable_pair_left hS hg0 hg
    refine Summable.of_norm_bounded ((h1.mul_left (B ^ (2 * n + 1) * K)).add
      (h2.mul_left (B ^ (2 * n + 1)))) (fun p => ?_)
    simp only [hT, Real.norm_eq_abs]
    have a0 := hg0 p.1; have b0 := hg0 p.2; have u0 := hU0 p.1 p.2
    have hE := exp_diff_le hM p.1 p.2
    have hE0 := Real.exp_pos (φ p.2 - φ p.1)
    have hpw : g p.1 ^ (2 * n + 1) ≤ B ^ (2 * n + 1) := pow_le_pow_left₀ a0 (hgB _) _
    have hBp : 0 ≤ B ^ (2 * n + 1) := pow_nonneg (hB0 p.1) _
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ g p.1 ^ (2 * n + 1)),
      abs_of_nonneg u0]
    have h3 : |Real.exp (φ p.2 - φ p.1) * g p.2 - g p.1| ≤ K * g p.2 + g p.1 := by
      rw [abs_le]; constructor
      · nlinarith
      · nlinarith
    calc g p.1 ^ (2 * n + 1) * (U p.1 p.2 * |Real.exp (φ p.2 - φ p.1) * g p.2 - g p.1|)
        ≤ B ^ (2 * n + 1) * (U p.1 p.2 * (K * g p.2 + g p.1)) := by
          gcongr
      _ = B ^ (2 * n + 1) * K * (U p.1 p.2 * g p.2) + B ^ (2 * n + 1) * (U p.1 p.2 * g p.1) := by
          ring
  -- the left side is `∑ T`
  have hL : ∑' z, g z ^ (2 * n + 1) * gen U φ g z = ∑' p, T p := by
    rw [hTs.tsum_prod' (fun z => hTs.prod_factor z)]
    refine tsum_congr fun z => ?_
    unfold gen
    rw [← tsum_mul_left]
  -- symmetrisation
  have hsw : ∑' p, T p = ∑' p : X × X, T p.swap := (tsum_swap' T).symm
  -- the right-hand summands
  set D : X × X → ℝ := fun p => U p.1 p.2 * (g p.1 ^ (n + 1) - g p.2 ^ (n + 1)) ^ 2 with hD
  set W : X × X → ℝ := fun p => U p.1 p.2 * dw φ p.1 p.2 * g p.1 ^ (2 * n + 2) with hW
  have hDs : Summable D := by
    have h1 := summable_pair_left hS (fun z => by have := hg0 z; positivity) hgq
    have h2 := summable_pair_right hS hUs (fun z => by have := hg0 z; positivity) hgq
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hU0 _ _) (sq_nonneg _))
      (fun p => ?_) ((h1.add h2).mul_left 2)
    simp only [hD]
    have e1 : g p.1 ^ (2 * n + 1 + 1) = (g p.1 ^ (n + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
    have e2 : g p.2 ^ (2 * n + 1 + 1) = (g p.2 ^ (n + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
    rw [e1, e2]
    have : (g p.1 ^ (n + 1) - g p.2 ^ (n + 1)) ^ 2 ≤
        2 * ((g p.1 ^ (n + 1)) ^ 2 + (g p.2 ^ (n + 1)) ^ 2) := by
      nlinarith [sq_nonneg (g p.1 ^ (n + 1) + g p.2 ^ (n + 1))]
    have u0 := hU0 p.1 p.2
    nlinarith
  have hWs : Summable W := by
    have h1 := summable_pair_left hS (fun z => by have := hg0 z; positivity) hgq
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      (h1.mul_left (2 * (K + 1) ^ 2))
    · simp only [hW]; have := hU0 p.1 p.2; have := dw_nonneg φ p.1 p.2; have := hg0 p.1
      positivity
    · simp only [hW]
      have := dw_le hM p.1 p.2
      have u0 := hU0 p.1 p.2
      have g0 : 0 ≤ g p.1 ^ (2 * n + 1 + 1) := by have := hg0 p.1; positivity
      rw [← hK] at this
      calc U p.1 p.2 * dw φ p.1 p.2 * g p.1 ^ (2 * n + 2)
          ≤ U p.1 p.2 * (2 * (K + 1) ^ 2) * g p.1 ^ (2 * n + 1 + 1) := by gcongr
        _ = 2 * (K + 1) ^ 2 * (U p.1 p.2 * g p.1 ^ (2 * n + 1 + 1)) := by ring
  -- pointwise
  have hpt : ∀ p : X × X, T p + T p.swap ≤ -(1 / (2 * m)) * D p + m * (W p + W p.swap) := by
    intro p
    simp only [hT, hD, hW, Prod.fst_swap, Prod.snd_swap]
    have hE0 := Real.exp_pos (φ p.2 - φ p.1)
    have hinv : Real.exp (φ p.1 - φ p.2) = 1 / Real.exp (φ p.2 - φ p.1) := by
      rw [one_div, ← Real.exp_neg]; ring_nf
    have hpi := point_ineq (hg0 p.1) (hg0 p.2) hE0 n
    rw [← hm] at hpi
    rw [hUs p.2 p.1, dw_symm φ p.2 p.1, hinv]
    have hdw : dw φ p.1 p.2 = (Real.exp (φ p.2 - φ p.1) - 1) ^ 2 +
        (1 / Real.exp (φ p.2 - φ p.1) - 1) ^ 2 := by
      unfold dw; rw [hinv]
    rw [hdw]
    have u0 := hU0 p.1 p.2
    have := mul_le_mul_of_nonneg_left hpi u0
    have e : g p.1 ^ (2 * n + 1) * (U p.1 p.2 * (Real.exp (φ p.2 - φ p.1) * g p.2 - g p.1)) +
        g p.2 ^ (2 * n + 1) * (U p.1 p.2 * (1 / Real.exp (φ p.2 - φ p.1) * g p.1 - g p.2)) =
        U p.1 p.2 * (g p.1 ^ (2 * n + 1) * (Real.exp (φ p.2 - φ p.1) * g p.2 - g p.1) +
          g p.2 ^ (2 * n + 1) * (g p.1 / Real.exp (φ p.2 - φ p.1) - g p.2)) := by ring
    rw [e]
    refine this.trans (le_of_eq ?_)
    ring
  -- sum the pointwise bound
  have hsum : 2 * ∑' p, T p ≤ -(1 / (2 * m)) * ∑' p, D p + m * (2 * ∑' p, W p) := by
    have hTsw : Summable (fun p : X × X => T p.swap) := hTs.prod_symm
    have hWsw : Summable (fun p : X × X => W p.swap) := hWs.prod_symm
    have h := Summable.tsum_le_tsum hpt (hTs.add hTsw)
      ((hDs.mul_left _).add ((hWs.add hWsw).mul_left m))
    rw [hTs.tsum_add hTsw, (hDs.mul_left _).tsum_add ((hWs.add hWsw).mul_left m),
      tsum_mul_left, tsum_mul_left, hWs.tsum_add hWsw, tsum_swap' W, ← hsw] at h
    linarith
  -- `∑ W ≤ 2Λ₂ ∑ g^{2m}`
  have hWb : ∑' p, W p ≤ 2 * Λ2 * ∑' z, g z ^ (2 * n + 2) := by
    rw [hWs.tsum_prod' (fun z => hWs.prod_factor z), ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun z => ?_) ?_ ((summable_gpow hg0 hgB hg (2 * n + 1)).mul_left _)
    · simp only [hW]
      have e : ∑' w, U z w * dw φ z w * g z ^ (2 * n + 2) =
          (∑' w, U z w * dw φ z w) * g z ^ (2 * n + 2) := tsum_mul_right
      rw [e]
      have := mul_le_mul_of_nonneg_right (hΛ z) (by have := hg0 z; positivity :
        0 ≤ g z ^ (2 * n + 2))
      linarith
    · exact hWs.prod
  rw [hL]
  have hD0 : 0 ≤ ∑' p, D p := tsum_nonneg fun p => mul_nonneg (hU0 _ _) (sq_nonneg _)
  have e : -(1 / (4 * m)) * ∑' p, D p = (1 / 2) * (-(1 / (2 * m)) * ∑' p, D p) := by
    field_simp; ring
  simp only [hD] at e
  rw [e]
  nlinarith

end MarkovHK.H5Core
end

section
/-!
# H5 core, step 4: the twisted trajectory and its derivative

For a symmetric transition kernel `U`, the heat series `hk U s z w = ∑ₙ poi(s, n) Uⁿ(z, w)` is
defined for every real `s`. For a bounded `φ` and `f` supported in a finite set `S`, the twisted
trajectory is `traj s z = ∑_{w ∈ S} e^{φ(w) − φ(z)} hk(s, z, w) f(w)`
(`= (e^{−φ} P_s e^{φ} f)(z)`).

* `hasDerivAt_traj`: `s ↦ traj s z` is differentiable with derivative `dtraj s z`;
* `hasDerivAt_sum_pow`: `s ↦ ∑_z traj(s, z)^{k+1}` is differentiable on all of `ℝ`, with
  derivative `∑_z (k+1) traj^k dtraj` (`hasDerivAt_tsum_of_isPreconnected`, dominated by the
  heat series at a larger time);
* `dtraj_eq_gen`: for `s ≥ 0`, `dtraj s = L^φ (traj s)` (the twisted generator of `H5CoreForm`).
-/

open DurrettProbability MarkovChain MarkovHK Set

namespace MarkovHK.H5Core

variable {X : Type*} [DecidableEq X]

/-- The derivative of the Poisson weight. -/
noncomputable def dpoi (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t) * ((n : ℝ) * t ^ (n - 1)) / n.factorial - poi t n

lemma hasDerivAt_poi (t : ℝ) (n : ℕ) : HasDerivAt (fun t => poi t n) (dpoi t n) t := by
  unfold dpoi poi
  have h1 : HasDerivAt (fun t => Real.exp (-t)) (Real.exp (-t) * -1) t :=
    (hasDerivAt_neg t).exp
  have h2 : HasDerivAt (fun t => t ^ n) ((n : ℝ) * t ^ (n - 1)) t := hasDerivAt_pow n t
  exact ((h1.mul h2).div_const (n.factorial : ℝ)).congr_deriv (by ring)

lemma abs_poi_le {y T : ℝ} (hy : y ∈ Ioo (-1) T) (hT : 1 ≤ T) (n : ℕ) :
    |poi y n| ≤ Real.exp (1 + T) * poi T n := by
  unfold poi
  have hyT : |y| ≤ T := abs_le.mpr ⟨by linarith [hy.1], hy.2.le⟩
  rw [abs_div, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), Nat.abs_cast]
  have hh : Real.exp (1 + T) * Real.exp (-T) = Real.exp 1 := by rw [← Real.exp_add]; ring_nf
  have e : Real.exp (1 + T) * (Real.exp (-T) * T ^ n / n.factorial) =
      Real.exp 1 * T ^ n / n.factorial := by
    rw [← hh]; ring
  rw [e]
  have h1 : Real.exp (-y) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [hy.1])
  have h2 : |y| ^ n ≤ T ^ n := pow_le_pow_left₀ (abs_nonneg _) hyT n
  exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le)
    (by positivity)

lemma abs_dpoi_le {y T : ℝ} (hy : y ∈ Ioo (-1) T) (hT : 1 ≤ T) (n : ℕ) :
    |dpoi y n| ≤ Real.exp (1 + T) * (poi T n * n + poi T n) := by
  unfold dpoi
  have hyT : |y| ≤ T := abs_le.mpr ⟨by linarith [hy.1], hy.2.le⟩
  have hp := abs_poi_le hy hT n
  have h1 : |Real.exp (-y) * ((n : ℝ) * y ^ (n - 1)) / n.factorial| ≤
      Real.exp (1 + T) * (poi T n * n) := by
    unfold poi
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), Nat.abs_cast,
      Nat.abs_cast]
    have hT0 : 0 ≤ T := by linarith
    have hpow : |y| ^ (n - 1) ≤ T ^ n := by
      calc |y| ^ (n - 1) ≤ T ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg _) hyT _
        _ ≤ T ^ n := pow_le_pow_right₀ hT (Nat.sub_le n 1)
    have hh : Real.exp (1 + T) * Real.exp (-T) = Real.exp 1 := by rw [← Real.exp_add]; ring_nf
    have e : Real.exp (1 + T) * (Real.exp (-T) * T ^ n / n.factorial * n) =
        Real.exp 1 * (n * T ^ n) / n.factorial := by
      rw [← hh]; ring
    rw [e]
    have h1 : Real.exp (-y) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [hy.1])
    have h2 : (n : ℝ) * |y| ^ (n - 1) ≤ n * T ^ n :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
    exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le)
      (by positivity)
  calc |Real.exp (-y) * ((n : ℝ) * y ^ (n - 1)) / n.factorial - poi y n|
      ≤ |Real.exp (-y) * ((n : ℝ) * y ^ (n - 1)) / n.factorial| + |poi y n| := abs_sub _ _
    _ ≤ Real.exp (1 + T) * (poi T n * n) + Real.exp (1 + T) * poi T n := add_le_add h1 hp
    _ = Real.exp (1 + T) * (poi T n * n + poi T n) := by ring

/-- The heat series (equal to `heatKernel U` for a transition kernel `U`). -/
noncomputable def hk (U : X → X → ℝ) (s : ℝ) (z w : X) : ℝ :=
  ∑' n, poi s n * stepProb U n z w

/-- Its termwise derivative. -/
noncomputable def dhk (U : X → X → ℝ) (s : ℝ) (z w : X) : ℝ :=
  ∑' n, dpoi s n * stepProb U n z w

lemma hk_eq_heat {U : X → X → ℝ} (hU : IsTransition U) (s : ℝ) (z w : X) :
    heatKernel U s z w = hk U s z w := by
  rw [heatKernel_eq, uniformize_eq_self hU]; rfl

lemma summable_poiw (T : ℝ) : Summable (fun n => poi T n * n + poi T n) :=
  (summable_poi_mul T).add (summable_poi T)

lemma poiw_nonneg {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : 0 ≤ poi T n * n + poi T n := by
  have := poi_nonneg hT n; positivity

section Deriv

variable {U : X → X → ℝ} (hS : IsSub U)
include hS

lemma summable_hk_terms {y T : ℝ} (hy : y ∈ Ioo (-1) T) (hT : 1 ≤ T) (z w : X) :
    Summable (fun n => poi y n * stepProb U n z w) := by
  refine Summable.of_norm_bounded ((summable_poi T).mul_left (Real.exp (1 + T))) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepProb_nonneg hS n z w)]
  calc |poi y n| * stepProb U n z w ≤ |poi y n| * 1 :=
        mul_le_mul_of_nonneg_left (stepProb_le_one hS n z w) (abs_nonneg _)
    _ ≤ Real.exp (1 + T) * poi T n := by rw [mul_one]; exact abs_poi_le hy hT n

lemma abs_dhk_le {y T : ℝ} (hy : y ∈ Ioo (-1) T) (hT : 1 ≤ T) (z w : X) :
    |dhk U y z w| ≤ Real.exp (1 + T) * ∑' n, (poi T n * n + poi T n) * stepProb U n z w := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hb : ∀ n, ‖dpoi y n * stepProb U n z w‖ ≤
      Real.exp (1 + T) * ((poi T n * n + poi T n) * stepProb U n z w) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepProb_nonneg hS n z w)]
    calc |dpoi y n| * stepProb U n z w
        ≤ Real.exp (1 + T) * (poi T n * n + poi T n) * stepProb U n z w :=
          mul_le_mul_of_nonneg_right (abs_dpoi_le hy hT n) (stepProb_nonneg hS n z w)
      _ = _ := by ring
  have hs : Summable (fun n => (poi T n * n + poi T n) * stepProb U n z w) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (poiw_nonneg hT0 n) (stepProb_nonneg hS n z w))
      (fun n => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hS n z w) (poiw_nonneg hT0 n)
        simpa using this) (summable_poiw T)
  unfold dhk
  calc |∑' n, dpoi y n * stepProb U n z w| ≤ ∑' n, ‖dpoi y n * stepProb U n z w‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
          (hs.mul_left _))
    _ ≤ ∑' n, Real.exp (1 + T) * ((poi T n * n + poi T n) * stepProb U n z w) :=
        Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
          (hs.mul_left _)) (hs.mul_left _)
    _ = _ := tsum_mul_left

lemma abs_hk_le {y T : ℝ} (hy : y ∈ Ioo (-1) T) (hT : 1 ≤ T) (z w : X) :
    |hk U y z w| ≤ Real.exp (1 + T) * ∑' n, (poi T n * n + poi T n) * stepProb U n z w := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hb : ∀ n, ‖poi y n * stepProb U n z w‖ ≤
      Real.exp (1 + T) * ((poi T n * n + poi T n) * stepProb U n z w) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepProb_nonneg hS n z w)]
    have h1 := abs_poi_le hy hT n
    have h2 : poi T n ≤ poi T n * n + poi T n := by
      have := poi_nonneg hT0 n; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
    calc |poi y n| * stepProb U n z w
        ≤ Real.exp (1 + T) * (poi T n * n + poi T n) * stepProb U n z w :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2
            (Real.exp_pos _).le)) (stepProb_nonneg hS n z w)
      _ = _ := by ring
  have hs : Summable (fun n => (poi T n * n + poi T n) * stepProb U n z w) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (poiw_nonneg hT0 n) (stepProb_nonneg hS n z w))
      (fun n => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hS n z w) (poiw_nonneg hT0 n)
        simpa using this) (summable_poiw T)
  unfold hk
  calc |∑' n, poi y n * stepProb U n z w| ≤ ∑' n, ‖poi y n * stepProb U n z w‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
          (hs.mul_left _))
    _ ≤ ∑' n, Real.exp (1 + T) * ((poi T n * n + poi T n) * stepProb U n z w) :=
        Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
          (hs.mul_left _)) (hs.mul_left _)
    _ = _ := tsum_mul_left

lemma hasDerivAt_hk {s T : ℝ} (hs : s ∈ Ioo (-1) T) (hT : 1 ≤ T) (z w : X) :
    HasDerivAt (fun s => hk U s z w) (dhk U s z w) s := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  unfold hk dhk
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n => Real.exp (1 + T) * (poi T n * n + poi T n))
    ((summable_poiw T).mul_left _) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_poi y n).mul_const _) (fun n y hy => ?_) hs
    (summable_hk_terms hS hs hT z w) hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepProb_nonneg hS n z w)]
  calc |dpoi y n| * stepProb U n z w ≤ |dpoi y n| * 1 :=
        mul_le_mul_of_nonneg_left (stepProb_le_one hS n z w) (abs_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact abs_dpoi_le hy hT n

end Deriv

/-- The twisted trajectory `e^{−φ} P_s (e^{φ} f)`, for `f` supported in `S`. -/
noncomputable def traj (U : X → X → ℝ) (φ : X → ℝ) (S : Finset X) (f : X → ℝ) (s : ℝ) (z : X) :
    ℝ :=
  ∑ w ∈ S, Real.exp (φ w - φ z) * hk U s z w * f w

/-- Its derivative. -/
noncomputable def dtraj (U : X → X → ℝ) (φ : X → ℝ) (S : Finset X) (f : X → ℝ) (s : ℝ) (z : X) :
    ℝ :=
  ∑ w ∈ S, Real.exp (φ w - φ z) * dhk U s z w * f w

section Traj

variable {U : X → X → ℝ} (hU : IsTransition U) (hUs : IsSymmetric U) {φ : X → ℝ} {M : ℝ}
  (hM : ∀ z, |φ z| ≤ M) (S : Finset X) (f : X → ℝ)

/-- The dominating function on the window `(−1, T)`. -/
noncomputable def domin (U : X → X → ℝ) (M : ℝ) (S : Finset X) (f : X → ℝ) (T : ℝ) (z : X) : ℝ :=
  ∑ w ∈ S, Real.exp (2 * M) * (Real.exp (1 + T) *
    ∑' n, (poi T n * n + poi T n) * stepProb U n z w) * |f w|

include hU hUs in
lemma summable_domin (T : ℝ) (hT : 0 ≤ T) : Summable (domin U M S f T) := by
  have hS := isSub_of_isTransition hU
  unfold domin
  refine summable_sum fun w _ => ?_
  refine Summable.mul_right _ (Summable.mul_left _ (Summable.mul_left _ ?_))
  have := summable_col_gen (poiw_nonneg hT) (summable_poiw T)
    (q := fun n z => stepProb U n w z) (fun n z => stepProb_nonneg hS n w z)
    (fun n => (isSub_stepProb hS n).2.1 w) (fun n => (isSub_stepProb hS n).2.2 w)
  refine this.congr fun z => tsum_congr fun n => ?_
  rw [stepProb_symm hS hUs n z w]

include hU hM in
lemma abs_traj_le {y T : ℝ} (hy : y ∈ Ioo (-1) T) (hT : 1 ≤ T) (z : X) :
    |traj U φ S f y z| ≤ domin U M S f T z := by
  have hS := isSub_of_isTransition hU
  unfold traj domin
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := exp_diff_le hM z w
  have h2 := abs_hk_le hS hy hT z w
  gcongr

include hU hM in
lemma abs_dtraj_le {y T : ℝ} (hy : y ∈ Ioo (-1) T) (hT : 1 ≤ T) (z : X) :
    |dtraj U φ S f y z| ≤ domin U M S f T z := by
  have hS := isSub_of_isTransition hU
  unfold dtraj domin
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := exp_diff_le hM z w
  have h2 := abs_dhk_le hS hy hT z w
  gcongr

/-- A uniform bound on the window. -/
noncomputable def ubd (M : ℝ) (S : Finset X) (f : X → ℝ) (T : ℝ) : ℝ :=
  ∑ w ∈ S, Real.exp (2 * M) * (Real.exp (1 + T) * (T + 1)) * |f w|

include hU in
lemma domin_le_ubd {T : ℝ} (hT : 0 ≤ T) (z : X) : domin U M S f T z ≤ ubd M S f T := by
  have hS := isSub_of_isTransition hU
  unfold domin ubd
  refine Finset.sum_le_sum fun w _ => ?_
  have hs : Summable (fun n => (poi T n * n + poi T n) * stepProb U n z w) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (poiw_nonneg hT n) (stepProb_nonneg hS n z w))
      (fun n => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hS n z w) (poiw_nonneg hT n)
        simpa using this) (summable_poiw T)
  have h : ∑' n, (poi T n * n + poi T n) * stepProb U n z w ≤ T + 1 := by
    calc ∑' n, (poi T n * n + poi T n) * stepProb U n z w ≤ ∑' n, (poi T n * n + poi T n) :=
          Summable.tsum_le_tsum (fun n => by
            have := mul_le_mul_of_nonneg_left (stepProb_le_one hS n z w) (poiw_nonneg hT n)
            simpa using this) hs (summable_poiw T)
      _ = T + 1 := by
          rw [(summable_poi_mul T).tsum_add (summable_poi T), (hasSum_poi_mul T).tsum_eq,
            tsum_poi]
  gcongr

include hU in
lemma hasDerivAt_traj {s T : ℝ} (hs : s ∈ Ioo (-1) T) (hT : 1 ≤ T) (z : X) :
    HasDerivAt (fun s => traj U φ S f s z) (dtraj U φ S f s z) s := by
  have hS := isSub_of_isTransition hU
  unfold traj dtraj
  refine HasDerivAt.fun_sum fun w _ => ?_
  exact ((hasDerivAt_hk hS hs hT z w).const_mul _).mul_const _

include hU hUs hM in
/-- **The derivative of `∑_z traj^{k+1}`.** -/
theorem hasDerivAt_sum_pow (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) :
    HasDerivAt (fun s => ∑' z, traj U φ S f s z ^ (k + 1))
      (∑' z, ((k : ℝ) + 1) * traj U φ S f s z ^ k * dtraj U φ S f s z) s := by
  set T := s + 1 with hTd
  have hT : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hs : s ∈ Ioo (-1) T := ⟨by linarith, by linarith⟩
  set B := ubd M S f T
  have hB : ∀ y ∈ Ioo (-1) T, ∀ z, |traj U φ S f y z| ≤ B := fun y hy z =>
    (abs_traj_le hU hM S f hy hT z).trans (domin_le_ubd hU S f hT0 z)
  have hds := summable_domin hU hUs S f (M := M) T hT0
  refine hasDerivAt_tsum_of_isPreconnected (g := fun z y => traj U φ S f y z ^ (k + 1))
    (g' := fun z y => ((k : ℝ) + 1) * traj U φ S f y z ^ k * dtraj U φ S f y z)
    (u := fun z => ((k : ℝ) + 1) * B ^ k * domin U M S f T z) (hds.mul_left _) isOpen_Ioo
    isPreconnected_Ioo (fun z y _ => ?_) (fun z y hy => ?_) hs ?_ hs
  · have := (hasDerivAt_pow (k + 1) (traj U φ S f y z)).comp y
      (hasDerivAt_traj hU (φ := φ) S f (by assumption) hT z)
    refine this.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have h1 := hB y hy z
    have h2 := abs_dtraj_le hU hM S f hy hT z
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    have hB0 : 0 ≤ B := (abs_nonneg _).trans h1
    gcongr
  · refine Summable.of_norm_bounded (hds.mul_left (B ^ k)) (fun z => ?_)
    rw [Real.norm_eq_abs, abs_pow, pow_succ]
    have h1 := hB s hs z
    have h2 := abs_traj_le hU hM S f hs hT z
    have hB0 : 0 ≤ B := (abs_nonneg _).trans h1
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 k) h2 (abs_nonneg _) (by positivity)

include hU hUs in
/-- For `s ≥ 0`, the derivative of the heat series is the generator applied to it. -/
lemma dhk_eq {s : ℝ} (hs0 : 0 ≤ s) (z w : X) :
    dhk U s z w = ∑' v, U z v * hk U s v w - hk U s z w := by
  have hS := isSub_of_isTransition hU
  have hs : s ∈ Ioo (-1) (s + 1) := ⟨by linarith, by linarith⟩
  have hT : (1 : ℝ) ≤ s + 1 := by linarith
  set a : ℕ → ℝ := fun n => stepProb U n z w with ha
  set A : ℕ → ℝ := fun n => Real.exp (-s) * ((n : ℝ) * s ^ (n - 1)) / n.factorial with hA
  have hpa : Summable (fun n => poi s n * a n) := summable_hk_terms hS hs hT z w
  have hda : Summable (fun n => dpoi s n * a n) := by
    refine Summable.of_norm_bounded (((summable_poiw (s + 1)).mul_left
      (Real.exp (1 + (s + 1))))) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepProb_nonneg hS n z w)]
    calc |dpoi s n| * a n ≤ |dpoi s n| * 1 :=
          mul_le_mul_of_nonneg_left (stepProb_le_one hS n z w) (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact abs_dpoi_le hs hT n
  have hAa : Summable (fun n => A n * a n) := by
    refine (hda.add hpa).congr fun n => ?_
    simp only [hA, dpoi]; ring
  have hshift : ∀ n, A (n + 1) = poi s n := by
    intro n
    simp only [hA, poi, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  have hA0 : A 0 = 0 := by simp [hA]
  have hsplit : dhk U s z w = ∑' n, A n * a n - ∑' n, poi s n * a n := by
    unfold dhk
    rw [← hAa.tsum_sub hpa]
    exact tsum_congr fun n => by simp only [hA, dpoi]; ring
  rw [hsplit, hAa.tsum_eq_zero_add, hA0, zero_mul, zero_add]
  have e1 : ∑' n, A (n + 1) * a (n + 1) = ∑' n, poi s n * ∑' v, stepProb U n w v * U z v := by
    refine tsum_congr fun n => ?_
    rw [hshift]
    congr 1
    simp only [ha, stepProb_succ]
    exact tsum_congr fun v => by rw [stepProb_symm hS hUs n v w]; ring
  rw [e1, tsum_comm_gen (fun n => poi_nonneg hs0 n) (summable_poi s)
    (q := fun n v => stepProb U n w v) (fun n v => stepProb_nonneg hS n w v)
    (fun n => (isSub_stepProb hS n).2.1 w) (fun n => (isSub_stepProb hS n).2.2 w)
    (fun v => hU.1 z v) (fun v => hS.le_one z v)]
  congr 1
  · refine tsum_congr fun v => ?_
    unfold hk
    rw [mul_comm]
    congr 1
    exact tsum_congr fun n => by rw [stepProb_symm hS hUs n w v]

include hU in
lemma hk_nonneg {s : ℝ} (hs0 : 0 ≤ s) (z w : X) : 0 ≤ hk U s z w := by
  rw [← hk_eq_heat hU]; exact heat_nonneg hU hs0 z w

include hU in
lemma hk_le_one {s : ℝ} (hs0 : 0 ≤ s) (z w : X) : hk U s z w ≤ 1 := by
  rw [← hk_eq_heat hU]; exact heat_le_one hU hs0 z w

include hU in
lemma traj_nonneg (hf0 : ∀ w, 0 ≤ f w) {s : ℝ} (hs0 : 0 ≤ s) (z : X) :
    0 ≤ traj U φ S f s z :=
  Finset.sum_nonneg fun w _ => mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (hk_nonneg hU hs0 z w)) (hf0 w)

include hU hM in
lemma traj_le (hf0 : ∀ w, 0 ≤ f w) {s : ℝ} (hs0 : 0 ≤ s) (z : X) :
    traj U φ S f s z ≤ ∑ w ∈ S, Real.exp (2 * M) * f w := by
  unfold traj
  refine Finset.sum_le_sum fun w _ => ?_
  have h1 := exp_diff_le hM z w
  have h2 := hk_le_one hU hs0 z w
  have h3 := hk_nonneg hU hs0 z w
  have h4 := hf0 w
  calc Real.exp (φ w - φ z) * hk U s z w * f w ≤ Real.exp (2 * M) * 1 * f w := by gcongr
    _ = _ := by ring

include hU hUs hM in
lemma summable_traj {s : ℝ} (hs0 : 0 ≤ s) : Summable (traj U φ S f s) :=
  Summable.of_norm_bounded (summable_domin hU hUs S f (M := M) (s + 1) (by linarith))
    (fun z => abs_traj_le hU hM S f (⟨by linarith, by linarith⟩ : s ∈ Ioo (-1) (s + 1))
      (by linarith) z)

include hU hUs in
/-- For `s ≥ 0`, `dtraj s = L^φ (traj s)`. -/
theorem dtraj_eq_gen {s : ℝ} (hs0 : 0 ≤ s) (z : X) :
    dtraj U φ S f s z = gen U φ (traj U φ S f s) z := by
  have hS := isSub_of_isTransition hU
  have hrow : ∀ w, Summable (fun v => U z v * hk U s v w) := fun w =>
    Summable.of_nonneg_of_le (fun v => mul_nonneg (hU.1 z v) (hk_nonneg hU hs0 v w))
      (fun v => by
        have := mul_le_mul_of_nonneg_left (hk_le_one hU hs0 v w) (hU.1 z v)
        simpa using this) (hU.2.1 z)
  -- the generator, split
  have hA : Summable (fun v => U z v * (Real.exp (φ v - φ z) * traj U φ S f s v)) := by
    have : ∀ v, U z v * (Real.exp (φ v - φ z) * traj U φ S f s v) =
        ∑ w ∈ S, Real.exp (φ w - φ z) * f w * (U z v * hk U s v w) := by
      intro v
      unfold traj
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have : Real.exp (φ v - φ z) * Real.exp (φ w - φ v) = Real.exp (φ w - φ z) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination (U z v * hk U s v w * f w) * this
    simp only [this]
    exact summable_sum fun w _ => (hrow w).mul_left _
  have hB : Summable (fun v => U z v * traj U φ S f s z) := (hU.2.1 z).mul_right _
  unfold gen
  have e : ∀ v, U z v * (Real.exp (φ v - φ z) * traj U φ S f s v - traj U φ S f s z) =
      U z v * (Real.exp (φ v - φ z) * traj U φ S f s v) - U z v * traj U φ S f s z :=
    fun v => by ring
  simp only [e]
  rw [hA.tsum_sub hB, tsum_mul_right, hU.2.2 z, one_mul]
  have e2 : ∀ v, U z v * (Real.exp (φ v - φ z) * traj U φ S f s v) =
      ∑ w ∈ S, Real.exp (φ w - φ z) * f w * (U z v * hk U s v w) := by
    intro v
    unfold traj
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have : Real.exp (φ v - φ z) * Real.exp (φ w - φ z - (φ v - φ z)) = Real.exp (φ w - φ z) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (φ w - φ v) = Real.exp (φ w - φ z - (φ v - φ z)) := by ring_nf
    rw [h2]
    linear_combination (U z v * hk U s v w * f w) * this
  simp only [e2]
  rw [Summable.tsum_finsetSum (fun w _ => (hrow w).mul_left _)]
  unfold dtraj traj
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dhk_eq hU hUs hs0 z w, tsum_mul_left]
  ring

lemma traj_zero (hS0 : ∀ z, z ∉ S → f z = 0) (z : X) : traj U φ S f 0 z = f z := by
  have hk0 : ∀ v w, hk U 0 v w = if v = w then 1 else 0 := by
    intro v w
    unfold hk
    rw [tsum_eq_single 0 (fun n hn => by
      simp [poi, zero_pow hn])]
    simp [poi, stepProb_zero]
  unfold traj
  simp only [hk0]
  by_cases hz : z ∈ S
  · rw [Finset.sum_eq_single z (fun w _ hw => by simp [Ne.symm hw]) (fun h => absurd hz h)]
    simp
  · rw [hS0 z hz]
    exact Finset.sum_eq_zero fun w hw => by
      have : z ≠ w := fun h => hz (h ▸ hw)
      simp [this]

end Traj

end MarkovHK.H5Core
end

section
/-!
# H5 core, step 5: the level inequalities (CKS (3.19), (3.20)) and one iteration step

`K` is a symmetric substochastic kernel, `U = uniformize K`, `φ` is bounded, `f ≥ 0` is supported in
the finite set `S`, and `F_s = traj U φ S f s = e^{−φ} P_s (e^{φ} f)`. Write
`P_n(s) = ∑_z F_s(z)^{2n+2}` (`levn`).

* `energy_eq`: `∑_{z,w} U(z,w)(h(z) − h(w))² = 2ℰ_K(h)`;
* `davies_bound`: `∑_w U(z,w) dw(z,w) ≤ 2Λ(φ)²` (from `daviesSq K φ ≠ ⊤`);
* `nash_ext'`: the Nash inequality for `h ≥ 0` bounded and summable (finite truncations);
* `dlev_le`: `P_n' ≤ −ℰ_K(F^{n+1}) + 4(n+1)²Λ₂ P_n` (the form inequality);
* `lev_gronwall`: `P_n(b) ≤ e^{4(n+1)²Λ₂(b−a)} P_n(a)` (CKS (3.19) at `n = 0`);
* `lev_step`: `P_{2n+1}(b) ≤ e^{(δ + 4(2n+2)²Λ₂)τ} (C/(βτ))^{1/β} (e^{4(n+1)²Λ₂τ} P_n(a))²`,
  `τ = b − a` (CKS (3.20) with Nash applied to `F^{n+1}`, and Lemma (3.21)).
-/

open DurrettProbability MarkovChain MarkovHK Set Filter Topology

namespace MarkovHK.H5Core

variable {X : Type*} [DecidableEq X]

lemma energy_eq (K : X → X → ℝ) (h : X → ℝ) :
    ∑' p : X × X, uniformize K p.1 p.2 * (h p.1 - h p.2) ^ 2 =
      2 * dirichletForm K (fun _ => 1) h := by
  unfold dirichletForm
  rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
  refine tsum_congr fun p => ?_
  unfold uniformize
  by_cases hp : p.1 = p.2
  · rw [hp]; simp
  · simp [hp]; ring

omit [DecidableEq X] in
lemma dirichletForm_nonneg' {K : X → X → ℝ} (hK0 : ∀ x y, 0 ≤ K x y) (h : X → ℝ) :
    0 ≤ dirichletForm K (fun _ => 1) h := by
  unfold dirichletForm
  exact mul_nonneg (by norm_num) (tsum_nonneg fun p => by
    have := hK0 p.1 p.2; positivity)

lemma davies_bound {K : X → X → ℝ} (hK0 : ∀ x y, 0 ≤ K x y) (hKr : ∀ x, Summable (K x))
    {φ : X → ℝ} {M : ℝ} (hM : ∀ z, |φ z| ≤ M) (hD : daviesSq K φ ≠ ⊤) (z : X) :
    ∑' w, uniformize K z w * dw φ z w ≤ 2 * (daviesSq K φ).toReal := by
  have e0 : ∀ w, uniformize K z w * dw φ z w = K z w * dw φ z w := by
    intro w
    unfold uniformize
    by_cases h : z = w
    · subst h; simp [dw]
    · simp [h]
  simp only [e0]
  set c := Real.exp (2 * M) + 1
  have hs1 : Summable (fun w => (Real.exp (φ w - φ z) - 1) ^ 2 * K z w) := by
    refine Summable.of_nonneg_of_le (fun w => mul_nonneg (sq_nonneg _) (hK0 z w)) (fun w => ?_)
      ((hKr z).mul_left (c ^ 2))
    have h1 := exp_diff_le hM z w
    have : (Real.exp (φ w - φ z) - 1) ^ 2 ≤ c ^ 2 :=
      sq_le_sq' (by linarith [Real.exp_pos (φ w - φ z), Real.exp_pos (2 * M)])
        (by linarith [Real.exp_pos (2 * M)])
    exact mul_le_mul_of_nonneg_right this (hK0 z w)
  have hs2 : Summable (fun w => (Real.exp (φ z - φ w) - 1) ^ 2 * K z w) := by
    refine Summable.of_nonneg_of_le (fun w => mul_nonneg (sq_nonneg _) (hK0 z w)) (fun w => ?_)
      ((hKr z).mul_left (c ^ 2))
    have h1 := exp_diff_le hM w z
    have : (Real.exp (φ z - φ w) - 1) ^ 2 ≤ c ^ 2 :=
      sq_le_sq' (by linarith [Real.exp_pos (φ z - φ w), Real.exp_pos (2 * M)])
        (by linarith [Real.exp_pos (2 * M)])
    exact mul_le_mul_of_nonneg_right this (hK0 z w)
  have b1 : ∑' w, (Real.exp (φ w - φ z) - 1) ^ 2 * K z w ≤ (daviesSq K φ).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hD,
      ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg (sq_nonneg _) (hK0 z w)) hs1,
      ← CarlenKusuokaStroock.H5.davies_term K φ z]
    unfold daviesSq
    exact le_trans (le_iSup (fun x => ENNReal.ofReal (Real.exp (-2 * φ x)) *
      carreDuChamp K (fun y => Real.exp (φ y)) x) z) (le_max_left _ _)
  have b2 : ∑' w, (Real.exp (φ z - φ w) - 1) ^ 2 * K z w ≤ (daviesSq K φ).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hD,
      ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg (sq_nonneg _) (hK0 z w)) hs2]
    have e : ∑' w, ENNReal.ofReal ((Real.exp (φ z - φ w) - 1) ^ 2 * K z w) =
        ENNReal.ofReal (Real.exp (2 * φ z)) * carreDuChamp K (fun y => Real.exp (-φ y)) z := by
      have := CarlenKusuokaStroock.H5.davies_term K (fun y => -φ y) z
      rw [show (2 : ℝ) * φ z = -2 * -φ z by ring, this]
      exact tsum_congr fun w => by ring_nf
    rw [e]
    unfold daviesSq
    exact le_trans (le_iSup (fun x => ENNReal.ofReal (Real.exp (2 * φ x)) *
      carreDuChamp K (fun y => Real.exp (-φ y)) x) z) (le_max_right _ _)
  unfold dw
  have e1 : ∀ w, K z w * ((Real.exp (φ w - φ z) - 1) ^ 2 + (Real.exp (φ z - φ w) - 1) ^ 2) =
      (Real.exp (φ w - φ z) - 1) ^ 2 * K z w + (Real.exp (φ z - φ w) - 1) ^ 2 * K z w :=
    fun w => by ring
  simp only [e1]
  rw [hs1.tsum_add hs2]
  linarith

/-- Nash for `h ≥ 0` bounded and summable, by finite truncations. -/
lemma nash_ext' {K : X → X → ℝ} (hK : MarkovHK.IsSub K) (hKs : IsSymmetric K) {C δ β : ℝ}
    (hβ : 0 < β) (hN : SatisfiesNash K C δ β) {h : X → ℝ} (h0 : ∀ z, 0 ≤ h z) {B : ℝ}
    (hB : ∀ z, h z ≤ B) (hs : Summable h) :
    normSq (fun _ => 1) h ^ (1 + β) ≤
      C * (dirichletForm K (fun _ => 1) h + δ * normSq (fun _ => 1) h) *
        (∑' x, |h x|) ^ (2 * β) := by
  classical
  set hF : Finset X → X → ℝ := fun F x => if x ∈ F then h x else 0 with hhF
  have hsq : Summable (fun x => h x ^ 2) := by
    have := summable_gpow h0 hB hs 1
    simpa using this
  have hN2 : Tendsto (fun F => normSq (fun _ => 1) (hF F)) atTop (𝓝 (normSq (fun _ => 1) h)) := by
    have hh := (hsq.mul_right 1).hasSum
    unfold normSq
    have e : ∀ F, ∑' x, hF F x ^ 2 * 1 = ∑ x ∈ F, h x ^ 2 * 1 := fun F => by
      rw [tsum_eq_sum (s := F) (fun x hx => by simp [hhF, hx])]
      exact Finset.sum_congr rfl fun x hx => by simp [hhF, hx]
    simp only [e]
    exact hh
  have hL : Tendsto (fun F => ∑' x, |hF F x|) atTop (𝓝 (∑' x, |h x|)) := by
    have hh := (hs.abs).hasSum
    have e : ∀ F, ∑' x, |hF F x| = ∑ x ∈ F, |h x| := fun F => by
      rw [tsum_eq_sum (s := F) (fun x hx => by simp [hhF, hx])]
      exact Finset.sum_congr rfl fun x hx => by simp [hhF, hx]
    simp only [e]
    exact hh
  have hbound : Summable (fun p : X × X => 2 * (K p.1 p.2 * h p.1 ^ 2 + K p.1 p.2 * h p.2 ^ 2)) :=
    ((summable_pair_left hK (fun z => sq_nonneg _) hsq).add
      (summable_pair_right hK hKs (fun z => sq_nonneg _) hsq)).mul_left 2
  have hE : Tendsto (fun F => dirichletForm K (fun _ => 1) (hF F)) atTop
      (𝓝 (dirichletForm K (fun _ => 1) h)) := by
    unfold dirichletForm
    refine Tendsto.const_mul _ ?_
    refine tendsto_tsum_of_dominated_convergence hbound (fun p => ?_) ?_
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop ({p.1, p.2} : Finset X)] with F hF'
      have h1 : p.1 ∈ F := hF' (by simp)
      have h2 : p.2 ∈ F := hF' (by simp)
      simp [hhF, h1, h2]
    · refine Filter.Eventually.of_forall fun F p => ?_
      have ha : 0 ≤ hF F p.1 ∧ hF F p.1 ≤ h p.1 := by
        simp only [hhF]; split_ifs
        · exact ⟨h0 _, le_rfl⟩
        · exact ⟨le_rfl, h0 _⟩
      have hb : 0 ≤ hF F p.2 ∧ hF F p.2 ≤ h p.2 := by
        simp only [hhF]; split_ifs
        · exact ⟨h0 _, le_rfl⟩
        · exact ⟨le_rfl, h0 _⟩
      have hK0 := hK.1 p.1 p.2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hK0) zero_le_one)]
      have h1 : (hF F p.1 - hF F p.2) ^ 2 ≤ 2 * h p.1 ^ 2 + 2 * h p.2 ^ 2 := by
        nlinarith [sq_nonneg (hF F p.1 + hF F p.2)]
      nlinarith
  have hlhs := hN2.rpow_const (Or.inr (by linarith : (0 : ℝ) ≤ 1 + β))
  have hrhs := ((hE.add (hN2.const_mul δ)).const_mul C).mul
    (hL.rpow_const (Or.inr (by linarith : (0 : ℝ) ≤ 2 * β)))
  refine le_of_tendsto_of_tendsto' hlhs hrhs fun F => ?_
  refine hN (hF F) ?_
  refine (F.finite_toSet).subset fun x hx => ?_
  by_contra hxF
  have hxF' : x ∉ F := fun h => hxF (Finset.mem_coe.mpr h)
  exact hx (by simp [hhF, hxF'])

/-- `P_n(s) = ∑_z F_s(z)^{2n+2}`. -/
noncomputable def levn (K : X → X → ℝ) (φ : X → ℝ) (S : Finset X) (f : X → ℝ) (n : ℕ) (s : ℝ) :
    ℝ :=
  ∑' z, traj (uniformize K) φ S f s z ^ (2 * n + 2)

/-- Its derivative. -/
noncomputable def dlev (K : X → X → ℝ) (φ : X → ℝ) (S : Finset X) (f : X → ℝ) (n : ℕ) (s : ℝ) :
    ℝ :=
  ∑' z, (((2 * n + 1 : ℕ) : ℝ) + 1) * traj (uniformize K) φ S f s z ^ (2 * n + 1) *
    dtraj (uniformize K) φ S f s z

section Level

variable {K : X → X → ℝ} (hK0 : ∀ x y, 0 ≤ K x y) (hKr : ∀ x, Summable (K x))
  (hK1 : ∀ x, ∑' y, K x y ≤ 1) (hKs : IsSymmetric K) {φ : X → ℝ} {M : ℝ}
  (hM : ∀ z, |φ z| ≤ M) (S : Finset X) {f : X → ℝ} (hf0 : ∀ z, 0 ≤ f z) {Λ2 : ℝ}
  (hΛ : ∀ z, ∑' w, uniformize K z w * dw φ z w ≤ 2 * Λ2)

include hK0 hKr hK1 hKs hM in
lemma hasDerivAt_levn (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) :
    HasDerivAt (levn K φ S f n) (dlev K φ S f n s) s := by
  have hU := isTransition_uniformize hK0 hKr hK1
  have hUs := uniformize_symm hKs
  exact hasDerivAt_sum_pow hU hUs hM S f (2 * n + 1) hs0

include hK0 hKr hK1 hKs hM hf0 hΛ in
/-- The level inequality `P_n' ≤ −ℰ_K(F^{n+1}) + 4(n+1)²Λ₂ P_n`. -/
lemma dlev_le (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) :
    dlev K φ S f n s ≤ -dirichletForm K (fun _ => 1)
        (fun z => traj (uniformize K) φ S f s z ^ (n + 1)) +
      4 * ((n : ℝ) + 1) ^ 2 * Λ2 * levn K φ S f n s := by
  have hU := isTransition_uniformize hK0 hKr hK1
  have hUs := uniformize_symm hKs
  set F := traj (uniformize K) φ S f s with hF
  have hF0 : ∀ z, 0 ≤ F z := traj_nonneg hU S f hf0 hs0
  have hFB : ∀ z, F z ≤ ∑ w ∈ S, Real.exp (2 * M) * f w := traj_le hU hM S f hf0 hs0
  have hFs : Summable F := summable_traj hU hUs hM S f hs0
  have hfi := form_ineq hU hUs hM hF0 hFB hFs hΛ n
  rw [energy_eq K (fun z => F z ^ (n + 1))] at hfi
  have e : dlev K φ S f n s = (2 * (n : ℝ) + 2) * ∑' z, F z ^ (2 * n + 1) * gen (uniformize K) φ F z := by
    unfold dlev
    rw [← tsum_mul_left]
    refine tsum_congr fun z => ?_
    rw [← hF, dtraj_eq_gen hU hUs S f hs0 z]
    push_cast
    ring
  rw [e]
  unfold levn
  rw [← hF]
  have hpos : (0 : ℝ) < 2 * n + 2 := by positivity
  have := mul_le_mul_of_nonneg_left hfi hpos.le
  have e2 : (2 * (n : ℝ) + 2) * (-(1 / (4 * ((n : ℝ) + 1))) *
      (2 * dirichletForm K (fun _ => 1) (fun z => F z ^ (n + 1))) +
        2 * ((n : ℝ) + 1) * Λ2 * ∑' z, F z ^ (2 * n + 2)) =
      -dirichletForm K (fun _ => 1) (fun z => F z ^ (n + 1)) +
        4 * ((n : ℝ) + 1) ^ 2 * Λ2 * ∑' z, F z ^ (2 * n + 2) := by
    field_simp
    ring
  linarith

include hK0 hKr hK1 hKs hM hf0 hΛ in
/-- Grönwall at level `n` (CKS (3.19) for `n = 0`). -/
lemma lev_gronwall (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    levn K φ S f n b ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2 * Λ2 * (b - a)) * levn K φ S f n a := by
  refine gronwall_le (u' := dlev K φ S f n) hab ?_ (fun s hs => hasDerivAt_levn hK0 hKr hK1 hKs
    hM S n (by linarith [hs.1])) (fun s hs => ?_)
  · intro s hs
    exact (hasDerivAt_levn hK0 hKr hK1 hKs hM S n (by linarith [hs.1])).continuousAt.continuousWithinAt
  · have h1 := dlev_le hK0 hKr hK1 hKs hM S hf0 hΛ n (s := s) (by linarith [hs.1])
    have h2 := dirichletForm_nonneg' hK0 (fun z => traj (uniformize K) φ S f s z ^ (n + 1))
    linarith

include hK0 hKr hK1 hf0 in
lemma levn_nonneg (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ levn K φ S f n s := by
  have hU := isTransition_uniformize hK0 hKr hK1
  exact tsum_nonneg fun z => pow_nonneg (traj_nonneg hU S f hf0 hs0 z) _

include hK0 hKr hK1 hKs hM hf0 in
/-- Nash applied to `F^{n+1}`: `P_{2n+1}^{1+β} ≤ C(ℰ_K(F^{2n+2}) + δ P_{2n+1}) P_n^{2β}`. -/
lemma lev_nash {C δ β : ℝ} (hβ : 0 < β) (hN : SatisfiesNash K C δ β) (n : ℕ) {s : ℝ}
    (hs0 : 0 ≤ s) :
    levn K φ S f (2 * n + 1) s ^ (1 + β) ≤
      C * (dirichletForm K (fun _ => 1) (fun z => traj (uniformize K) φ S f s z ^ (2 * n + 1 + 1)) +
        δ * levn K φ S f (2 * n + 1) s) * levn K φ S f n s ^ (2 * β) := by
  have hU := isTransition_uniformize hK0 hKr hK1
  have hUs := uniformize_symm hKs
  set F := traj (uniformize K) φ S f s with hF
  have hF0 : ∀ z, 0 ≤ F z := traj_nonneg hU S f hf0 hs0
  have hFB : ∀ z, F z ≤ ∑ w ∈ S, Real.exp (2 * M) * f w := traj_le hU hM S f hf0 hs0
  have hFs : Summable F := summable_traj hU hUs hM S f hs0
  set h : X → ℝ := fun z => F z ^ (2 * n + 1 + 1) with hh
  have h0 : ∀ z, 0 ≤ h z := fun z => pow_nonneg (hF0 z) _
  have hB : ∀ z, h z ≤ (∑ w ∈ S, Real.exp (2 * M) * f w) ^ (2 * n + 1 + 1) := fun z =>
    pow_le_pow_left₀ (hF0 z) (hFB z) _
  have hs : Summable h := summable_gpow hF0 hFB hFs (2 * n + 1)
  have hKsub : MarkovHK.IsSub K := ⟨hK0, hKr, hK1⟩
  have hn := nash_ext' hKsub hKs hβ hN h0 hB hs
  have e1 : normSq (fun _ => 1) h = levn K φ S f (2 * n + 1) s := by
    unfold normSq levn
    rw [← hF]
    refine tsum_congr fun z => ?_
    simp only [hh, mul_one]
    rw [← pow_mul]; ring_nf
  have e2 : ∑' x, |h x| = levn K φ S f n s := by
    unfold levn
    rw [← hF]
    refine tsum_congr fun z => ?_
    rw [abs_of_nonneg (h0 z)]
  rw [e1, e2] at hn
  exact hn

include hK0 hKr hK1 hKs hM hf0 hΛ in
/-- **One iteration step** (CKS (3.20) + Lemma (3.21) on the window `[a, b]`). -/
theorem lev_step {C δ β : ℝ} (hC : 0 < C) (hβ : 0 < β) (hδ : 0 ≤ δ) (hΛ0 : 0 ≤ Λ2)
    (hN : SatisfiesNash K C δ β) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    levn K φ S f (2 * n + 1) b ≤
      Real.exp ((δ + 4 * (((2 * n + 1 : ℕ) : ℝ) + 1) ^ 2 * Λ2) * (b - a)) *
        (C / (β * (b - a))) ^ (1 / β) *
          (Real.exp (4 * ((n : ℝ) + 1) ^ 2 * Λ2 * (b - a)) * levn K φ S f n a) ^ 2 := by
  set τ := b - a with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  set V := Real.exp (4 * ((n : ℝ) + 1) ^ 2 * Λ2 * τ) * levn K φ S f n a with hVd
  have hla := levn_nonneg (φ := φ) hK0 hKr hK1 S hf0 n ha
  have hV : ∀ s ∈ Icc a b, levn K φ S f n s ≤ V := by
    intro s hs
    refine (lev_gronwall hK0 hKr hK1 hKs hM S hf0 hΛ n ha hs.1).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hla
    have : s - a ≤ τ := by rw [hτ]; linarith [hs.2]
    have : 0 ≤ 4 * ((n : ℝ) + 1) ^ 2 * Λ2 := by positivity
    nlinarith
  have hRHS0 : 0 ≤ Real.exp ((δ + 4 * (((2 * n + 1 : ℕ) : ℝ) + 1) ^ 2 * Λ2) * τ) *
      (C / (β * τ)) ^ (1 / β) * V ^ 2 := by positivity
  rcases hla.eq_or_lt with h0 | hpos
  · -- degenerate case
    have hVz : V = 0 := by rw [hVd, ← h0, mul_zero]
    have hb0 : levn K φ S f n b = 0 := le_antisymm (by
      have := hV b (right_mem_Icc.mpr hab.le); rwa [hVz] at this)
      (levn_nonneg (φ := φ) hK0 hKr hK1 S hf0 n (by linarith))
    have hn := lev_nash hK0 hKr hK1 hKs hM S hf0 hβ hN n (s := b) (by linarith)
    rw [hb0, Real.zero_rpow (by positivity), mul_zero] at hn
    have hu0 := levn_nonneg (φ := φ) hK0 hKr hK1 S hf0 (2 * n + 1) (s := b) (by linarith)
    have : levn K φ S f (2 * n + 1) b = 0 := by
      by_contra hne
      have := Real.rpow_pos_of_pos (lt_of_le_of_ne hu0 (Ne.symm hne)) (1 + β)
      linarith
    rw [this]; exact hRHS0
  · have hVpos : 0 < V := by positivity
    set κ := 1 / (C * V ^ (2 * β)) with hκ
    have hκ0 : 0 < κ := by positivity
    set lam := δ + 4 * (((2 * n + 1 : ℕ) : ℝ) + 1) ^ 2 * Λ2 with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hode := nash_ode_exp (u := levn K φ S f (2 * n + 1)) (u' := dlev K φ S f (2 * n + 1))
      hab hκ0 hβ hlam0 ?_ ?_ ?_ ?_
    · rw [← hτ] at hode
      refine hode.trans (le_of_eq ?_)
      rw [show Real.exp (lam * τ) * (C / (β * τ)) ^ (1 / β) * V ^ 2 =
        Real.exp (lam * τ) * ((C / (β * τ)) ^ (1 / β) * V ^ 2) by ring]
      congr 1
      -- `(βκτ)^{−1/β} = (C/(βτ))^{1/β} V²`
      have e1 : β * κ * τ = (C * V ^ (2 * β) / (β * τ))⁻¹ := by
        rw [hκ]; field_simp
      have hX : 0 < C * V ^ (2 * β) / (β * τ) := by positivity
      rw [e1, Real.inv_rpow hX.le, ← Real.rpow_neg hX.le, neg_div, neg_neg]
      rw [show C * V ^ (2 * β) / (β * τ) = C / (β * τ) * V ^ (2 * β) by ring,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hVpos.le,
        show 2 * β * (1 / β) = (2 : ℕ) by field_simp; norm_num, Real.rpow_natCast]
    · intro s hs
      exact (hasDerivAt_levn hK0 hKr hK1 hKs hM S (2 * n + 1)
        (by linarith [hs.1])).continuousAt.continuousWithinAt
    · intro s hs
      exact levn_nonneg (φ := φ) hK0 hKr hK1 S hf0 (2 * n + 1) (by linarith [hs.1])
    · intro s hs
      exact hasDerivAt_levn hK0 hKr hK1 hKs hM S (2 * n + 1) (by linarith [hs.1])
    · intro s hs
      have hs0 : 0 ≤ s := by linarith [hs.1]
      have hd := dlev_le hK0 hKr hK1 hKs hM S hf0 hΛ (2 * n + 1) hs0
      have hn := lev_nash hK0 hKr hK1 hKs hM S hf0 hβ hN n hs0
      set E := dirichletForm K (fun _ => 1) (fun z => traj (uniformize K) φ S f s z ^ (2 * n + 1 + 1))
      set u := levn K φ S f (2 * n + 1) s
      have hE0 : 0 ≤ E := dirichletForm_nonneg' hK0 _
      have hu0 : 0 ≤ u := levn_nonneg (φ := φ) hK0 hKr hK1 S hf0 (2 * n + 1) hs0
      have hvs := hV s (Ioo_subset_Icc_self hs)
      have hv0 := levn_nonneg (φ := φ) hK0 hKr hK1 S hf0 n hs0
      have hpow : levn K φ S f n s ^ (2 * β) ≤ V ^ (2 * β) :=
        Real.rpow_le_rpow hv0 hvs (by positivity)
      have h1 : u ^ (1 + β) ≤ C * (E + δ * u) * V ^ (2 * β) :=
        hn.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      have h2 : κ * u ^ (1 + β) ≤ E + δ * u := by
        rw [hκ, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        linarith
      rw [hlam]
      push_cast at hd ⊢
      nlinarith

end Level

end MarkovHK.H5Core
end

section
/-!
# H5 core, step 6: the bookkeeping of the iteration `p_k = 2^{k+1}` (CKS p. 271)

* `iter_bound`: if `0 ≤ a_k`, `a_0 ≤ A₀` and `a_{k+1} ≤ c_k a_k²` (`c_k > 0`), then
  `a_k ≤ (√A₀ · exp(∑_{j<k} log c_j / 2^{j+2}))^{2^{k+1}}`;
* `sum_geom1`, `sum_geom2`: the two finite geometric sums;
* `root_le`: from `x^N ≤ e^c Y^N` to `x ≤ e^{c/N} Y`;
* `le_of_forall_exp`: from `x ≤ W e^{ε/2^{k+1}}` for all `k` to `x ≤ W`.
-/

open Finset Filter Topology

namespace MarkovHK.H5Core

lemma iter_bound {a c : ℕ → ℝ} {A0 : ℝ} (ha0 : ∀ k, 0 ≤ a k) (hA0 : a 0 ≤ A0)
    (hc : ∀ k, 0 < c k) (hstep : ∀ k, a (k + 1) ≤ c k * a k ^ 2) (k : ℕ) :
    a k ≤ (Real.sqrt A0 * Real.exp (∑ j ∈ range k, Real.log (c j) / 2 ^ (j + 2))) ^ (2 ^ (k + 1)) := by
  have hA00 : 0 ≤ A0 := (ha0 0).trans hA0
  induction k with
  | zero =>
    simp only [range_zero, sum_empty, Real.exp_zero, mul_one, zero_add, pow_one]
    rw [Real.sq_sqrt hA00]; exact hA0
  | succ k ih =>
    obtain ⟨E, hE⟩ : ∃ E, E = Real.sqrt A0 * Real.exp (∑ j ∈ range k, Real.log (c j) / 2 ^ (j + 2)) :=
      ⟨_, rfl⟩
    rw [← hE] at ih
    have hE0 : 0 ≤ E := by rw [hE]; positivity
    have h1 : a k ^ 2 ≤ (E ^ (2 ^ (k + 1))) ^ 2 := pow_le_pow_left₀ (ha0 k) ih 2
    have h2 := (hstep k).trans (mul_le_mul_of_nonneg_left h1 (hc k).le)
    refine h2.trans (le_of_eq ?_)
    have e : ((2 ^ (k + 1 + 1) : ℕ) : ℝ) * (Real.log (c k) / 2 ^ (k + 2)) = Real.log (c k) := by
      push_cast; field_simp
    calc c k * (E ^ (2 ^ (k + 1))) ^ 2 = c k * E ^ (2 ^ (k + 1 + 1)) := by
          rw [← pow_mul]; ring_nf
      _ = (E * Real.exp (Real.log (c k) / 2 ^ (k + 2))) ^ (2 ^ (k + 1 + 1)) := by
          rw [mul_pow, ← Real.exp_nat_mul, e, Real.exp_log (hc k)]; ring
      _ = _ := by rw [sum_range_succ, Real.exp_add, ← mul_assoc, ← hE]

lemma sum_geom1 (k : ℕ) : ∑ j ∈ range k, (1 : ℝ) / 2 ^ (j + 2) = 1 / 2 - 1 / 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ, ih]
    field_simp
    ring

lemma sum_geom2 (k : ℕ) :
    ∑ j ∈ range k, ((j : ℝ) + 1) / 2 ^ (j + 2) = 1 - ((k : ℝ) + 2) / 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- `∑_{j<k} (Γ + (j+1)κ)/2^{j+2} ≤ Γ/2 + κ + |Γ|/2^{k+1}` for `κ ≥ 0`. -/
lemma sum_lin_le (Γ κ : ℝ) (hκ : 0 ≤ κ) (k : ℕ) :
    ∑ j ∈ range k, (Γ + ((j : ℝ) + 1) * κ) / 2 ^ (j + 2) ≤ Γ / 2 + κ + |Γ| / 2 ^ (k + 1) := by
  have e : ∑ j ∈ range k, (Γ + ((j : ℝ) + 1) * κ) / 2 ^ (j + 2) =
      Γ * ∑ j ∈ range k, (1 : ℝ) / 2 ^ (j + 2) + κ * ∑ j ∈ range k, ((j : ℝ) + 1) / 2 ^ (j + 2) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [e, sum_geom1, sum_geom2]
  have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have h3 : 0 ≤ κ * (((k : ℝ) + 2) / 2 ^ (k + 1)) := by positivity
  have h4 : -Γ / 2 ^ (k + 1) ≤ |Γ| / 2 ^ (k + 1) :=
    div_le_div_of_nonneg_right (neg_le_abs Γ) h2.le
  have e2 : Γ * (1 / 2 - 1 / 2 ^ (k + 1)) = Γ / 2 + -Γ / 2 ^ (k + 1) := by ring
  have e3 : κ * (1 - ((k : ℝ) + 2) / 2 ^ (k + 1)) = κ - κ * (((k : ℝ) + 2) / 2 ^ (k + 1)) := by ring
  rw [e2, e3]
  linarith

/-- Roots. -/
lemma root_le {x Y c : ℝ} (hx : 0 ≤ x) (hY : 0 ≤ Y) {N : ℕ} (hN : N ≠ 0)
    (h : x ^ N ≤ Real.exp c * Y ^ N) : x ≤ Real.exp (c / N) * Y := by
  have hN' : (0 : ℝ) < N := by positivity
  have e : (Real.exp (c / N) * Y) ^ N = Real.exp c * Y ^ N := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    field_simp
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ hx (by positivity) hN).mp h

/-- The limit `k → ∞`. -/
lemma le_of_forall_exp {x W ε : ℝ} (h : ∀ k : ℕ, x ≤ W * Real.exp (ε / 2 ^ (k + 1))) : x ≤ W := by
  have ht : Tendsto (fun k : ℕ => W * Real.exp (ε / 2 ^ (k + 1))) atTop (𝓝 (W * Real.exp 0)) := by
    refine Tendsto.const_mul _ ((Real.continuous_exp.tendsto 0).comp ?_)
    have h2 : Tendsto (fun k : ℕ => (ε / 2) * (1 / 2 : ℝ) ^ k) atTop (𝓝 ((ε / 2) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    have h3 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [pow_succ]
    field_simp
    linear_combination ε * h3
  rw [Real.exp_zero, mul_one] at ht
  exact ge_of_tendsto' ht h

end MarkovHK.H5Core
end

section
/-!
# H5 core, step 7: the `L² → L^∞` bound for the twisted semigroup, `CoreL2`, and H5

`sup_bound`: for `f ≥ 0` finitely supported and `t > 0`,
`(e^{−φ} P_t e^{φ} f)(y)² ≤ e^{(8/3)Λ₂t} ‖f‖₂² · e^{Γ + 2κ}`, `Γ = δt + 6Λ₂t + (1/β) log(C/(βt))`,
`κ = log 4 / β`, by the iteration of `lev_step` over the levels `2^{k+1}` on the windows
`[t − (t/3)4^{−k}, t − (t/3)4^{−k−1}]` (CKS p. 271), started from CKS (3.19) on `[0, 2t/3]`.
Then `CoreL2` by duality (`P^{−ψ}` is the adjoint of `P^{ψ}`), and H5 by
`heatKernel_le_exp_davies_of_core`.
-/


open DurrettProbability MarkovChain MarkovHK Set Finset

namespace MarkovHK.H5Core

variable {X : Type*} [DecidableEq X]

lemma nat_two_pow_sub (k : ℕ) : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
  have h := Nat.one_le_two_pow (n := k)
  rw [pow_succ]; omega

lemma cast_two_pow_sub (k : ℕ) : (((2 ^ k - 1 : ℕ) : ℝ) + 1) = 2 ^ k := by
  have h := Nat.one_le_two_pow (n := k)
  rw [Nat.cast_sub h]; push_cast; ring

lemma cast_two_pow_sub' (k : ℕ) : ((((2 * (2 ^ k - 1) + 1) : ℕ) : ℝ) + 1) = 2 ^ (k + 1) := by
  rw [nat_two_pow_sub, cast_two_pow_sub]

lemma exp_two_pow_sub (k : ℕ) : 2 * (2 ^ k - 1) + 2 = 2 ^ (k + 1) := by
  have h := Nat.one_le_two_pow (n := k)
  rw [pow_succ]; omega

section Sup

variable {K : X → X → ℝ} (hK0 : ∀ x y, 0 ≤ K x y) (hKr : ∀ x, Summable (K x))
  (hK1 : ∀ x, ∑' y, K x y ≤ 1) (hKs : IsSymmetric K) {φ : X → ℝ} {M : ℝ}
  (hM : ∀ z, |φ z| ≤ M) (S : Finset X) {f : X → ℝ} (hf0 : ∀ z, 0 ≤ f z)
  (hfS : ∀ z, z ∉ S → f z = 0) {Λ2 : ℝ} (hΛ0 : 0 ≤ Λ2)
  (hΛ : ∀ z, ∑' w, uniformize K z w * dw φ z w ≤ 2 * Λ2)

include hK0 hKr hK1 hKs hM hf0 hfS hΛ0 hΛ in
/-- **The `L² → L^∞` bound** for the twisted semigroup. -/
theorem sup_bound {C δ β : ℝ} (hC : 0 < C) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hN : SatisfiesNash K C δ β) {t : ℝ} (ht : 0 < t) (y : X) :
    traj (uniformize K) φ S f t y ^ 2 ≤
      (Real.exp (4 * Λ2 * (2 * t / 3)) * ∑' z, f z ^ 2) *
        Real.exp ((δ * t + 6 * Λ2 * t + (1 / β) * Real.log (C / (β * t))) +
          2 * (Real.log 4 / β)) := by
  have hU := isTransition_uniformize hK0 hKr hK1
  have hUs := uniformize_symm hKs
  set F := traj (uniformize K) φ S f with hF
  -- times, levels
  set sk : ℕ → ℝ := fun k => t - (t / 3) / 4 ^ k with hsk
  set τ : ℕ → ℝ := fun k => t / 4 ^ (k + 1) with hτ
  have hsk_succ : ∀ k, sk (k + 1) - sk k = τ k := by
    intro k; simp only [hsk, hτ]; field_simp; ring
  have hτ0 : ∀ k, 0 < τ k := fun k => by simp only [hτ]; positivity
  have hsk0 : ∀ k, 0 ≤ sk k := by
    intro k; simp only [hsk]
    have : (t / 3) / 4 ^ k ≤ t / 3 := div_le_self (by positivity) (one_le_pow₀ (by norm_num))
    linarith
  set nk : ℕ → ℕ := fun k => 2 ^ k - 1 with hnk
  set a : ℕ → ℝ := fun k => levn K φ S f (nk k) (sk k) with ha
  set c : ℕ → ℝ := fun k =>
    Real.exp ((δ + 4 * ((((2 * nk k + 1) : ℕ) : ℝ) + 1) ^ 2 * Λ2) * τ k) *
      (C / (β * τ k)) ^ (1 / β) * Real.exp (4 * (((nk k : ℕ) : ℝ) + 1) ^ 2 * Λ2 * τ k) ^ 2
    with hc
  have hc0 : ∀ k, 0 < c k := fun k => by
    simp only [hc]; have := hτ0 k; positivity
  have ha0 : ∀ k, 0 ≤ a k := fun k => levn_nonneg (φ := φ) hK0 hKr hK1 S hf0 _ (hsk0 k)
  -- the step
  have hstep : ∀ k, a (k + 1) ≤ c k * a k ^ 2 := by
    intro k
    have hlt : sk k < sk (k + 1) := by linarith [hsk_succ k, hτ0 k]
    have h := lev_step hK0 hKr hK1 hKs hM S hf0 hΛ hC hβ hδ hΛ0 hN (nk k) (hsk0 k) hlt
    rw [hsk_succ k] at h
    have hidx : 2 * nk k + 1 = nk (k + 1) := by simp only [hnk]; exact nat_two_pow_sub k
    simp only [ha, ← hidx]
    refine h.trans (le_of_eq ?_)
    simp only [hc]
    ring
  -- the start: CoreL2 (3.19) on `[0, 2t/3]`
  set A0 := Real.exp (4 * Λ2 * (2 * t / 3)) * ∑' z, f z ^ 2 with hA0
  have ha00 : a 0 ≤ A0 := by
    have h := lev_gronwall hK0 hKr hK1 hKs hM S hf0 hΛ 0 (a := 0) (b := sk 0) le_rfl (hsk0 0)
    have e1 : sk 0 = 2 * t / 3 := by simp only [hsk]; ring
    have e2 : levn K φ S f 0 0 = ∑' z, f z ^ 2 := by
      unfold levn
      exact tsum_congr fun z => by rw [traj_zero S f hfS z]
    simp only [ha, hnk, pow_zero, Nat.sub_self]
    rw [e2] at h
    refine h.trans (le_of_eq ?_)
    rw [hA0, e1]; congr 1; push_cast; ring_nf
  have hiter := iter_bound ha0 ha00 hc0 hstep
  -- the per-step logarithm
  set Γ := δ * t + 6 * Λ2 * t + (1 / β) * Real.log (C / (β * t)) with hΓ
  set κ := Real.log 4 / β with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg (Real.log_nonneg (by norm_num)) hβ.le
  have hlogc : ∀ j, Real.log (c j) ≤ Γ + ((j : ℝ) + 1) * κ := by
    intro j
    have hτj := hτ0 j
    have hB : 0 < C / (β * τ j) := by positivity
    simp only [hc]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_pow, Real.log_exp, Real.log_rpow hB]
    have e1 : C / (β * τ j) = C / (β * t) * 4 ^ (j + 1) := by
      simp only [hτ]; field_simp
    rw [e1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [cast_two_pow_sub' j]
    have e2 : (((nk j : ℕ) : ℝ) + 1) = 2 ^ j := cast_two_pow_sub j
    rw [e2]
    have e3 : (4 * ((2 : ℝ) ^ (j + 1)) ^ 2 * Λ2) * τ j + 2 * (4 * ((2 : ℝ) ^ j) ^ 2 * Λ2 * τ j) =
        6 * Λ2 * t := by
      simp only [hτ]
      rw [← pow_mul, ← pow_mul, show (4 : ℝ) ^ (j + 1) = 2 ^ ((j + 1) * 2) by
        rw [mul_comm, pow_mul]; norm_num]
      field_simp
      ring_nf
    have e4 : δ * τ j ≤ δ * t := by
      simp only [hτ]
      exact mul_le_mul_of_nonneg_left (div_le_self ht.le (one_le_pow₀ (by norm_num))) hδ
    rw [hΓ, hκ]
    push_cast
    have e5 : (δ + 4 * ((2 : ℝ) ^ (j + 1)) ^ 2 * Λ2) * τ j +
        1 / β * (Real.log (C / (β * t)) + ((j : ℝ) + 1) * Real.log 4) +
        2 * (4 * ((2 : ℝ) ^ j) ^ 2 * Λ2 * τ j) =
        δ * τ j + ((4 * ((2 : ℝ) ^ (j + 1)) ^ 2 * Λ2) * τ j + 2 * (4 * ((2 : ℝ) ^ j) ^ 2 * Λ2 * τ j)) +
          1 / β * Real.log (C / (β * t)) + ((j : ℝ) + 1) * (Real.log 4 / β) := by ring
    rw [e5, e3]
    linarith
  have hsum : ∀ k, ∑ j ∈ range k, Real.log (c j) / 2 ^ (j + 2) ≤ Γ / 2 + κ + |Γ| / 2 ^ (k + 1) := by
    intro k
    refine le_trans (sum_le_sum fun j _ => ?_) (sum_lin_le Γ κ hκ0 k)
    exact div_le_div_of_nonneg_right (hlogc j) (by positivity)
  -- the final time
  have hFt0 : ∀ z, 0 ≤ F t z := traj_nonneg hU S f hf0 ht.le
  have hFtB : ∀ z, F t z ≤ ∑ w ∈ S, Real.exp (2 * M) * f w := traj_le hU hM S f hf0 ht.le
  have hFts : Summable (F t) := summable_traj hU hUs hM S f ht.le
  have hfin : ∀ k, F t y ≤ Real.sqrt A0 * Real.exp (Γ / 2 + κ) *
      Real.exp ((|Γ| + 4 / 3 * Λ2 * t) / 2 ^ (k + 1)) := by
    intro k
    set N := 2 * nk k + 2 with hN'
    have hNe : N = 2 ^ (k + 1) := by simp only [hN', hnk]; exact exp_two_pow_sub k
    have h1 : F t y ^ N ≤ levn K φ S f (nk k) t := by
      unfold levn
      rw [← hF]
      exact (summable_gpow hFt0 hFtB hFts (2 * nk k + 1)).le_tsum y
        (fun z _ => pow_nonneg (hFt0 z) _)
    have hle : sk k ≤ t := by
      simp only [hsk]; have : 0 ≤ (t / 3) / 4 ^ k := by positivity
      linarith
    have h2 := lev_gronwall hK0 hKr hK1 hKs hM S hf0 hΛ (nk k) (hsk0 k) hle
    have e2 : (((nk k : ℕ) : ℝ) + 1) = 2 ^ k := cast_two_pow_sub k
    rw [e2] at h2
    have e3 : 4 * ((2 : ℝ) ^ k) ^ 2 * Λ2 * (t - sk k) = 4 / 3 * Λ2 * t := by
      simp only [hsk]
      rw [← pow_mul, show (4 : ℝ) ^ k = 2 ^ (k * 2) by rw [mul_comm, pow_mul]; norm_num]
      field_simp
      ring
    rw [e3] at h2
    set E := Real.sqrt A0 * Real.exp (∑ j ∈ range k, Real.log (c j) / 2 ^ (j + 2)) with hE
    have hE0 : 0 ≤ E := by positivity
    have h3 : F t y ^ N ≤ Real.exp (4 / 3 * Λ2 * t) * E ^ N := by
      refine h1.trans (h2.trans ?_)
      rw [hNe]
      exact mul_le_mul_of_nonneg_left (hiter k) (Real.exp_pos _).le
    have hN0 : N ≠ 0 := by simp only [hN']; omega
    have h4 := root_le (hFt0 y) hE0 hN0 h3
    have hNr : (N : ℝ) = 2 ^ (k + 1) := by rw [hNe]; push_cast; ring
    rw [hNr] at h4
    have h5 : E ≤ Real.sqrt A0 * Real.exp (Γ / 2 + κ + |Γ| / 2 ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hsum k)) (Real.sqrt_nonneg _)
    calc F t y ≤ Real.exp (4 / 3 * Λ2 * t / 2 ^ (k + 1)) * E := h4
      _ ≤ Real.exp (4 / 3 * Λ2 * t / 2 ^ (k + 1)) *
          (Real.sqrt A0 * Real.exp (Γ / 2 + κ + |Γ| / 2 ^ (k + 1))) :=
          mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
      _ = Real.sqrt A0 * Real.exp (Γ / 2 + κ) *
          Real.exp ((|Γ| + 4 / 3 * Λ2 * t) / 2 ^ (k + 1)) := by
          have hx : Real.exp (4 / 3 * Λ2 * t / 2 ^ (k + 1)) *
              Real.exp (Γ / 2 + κ + |Γ| / 2 ^ (k + 1)) =
              Real.exp (Γ / 2 + κ) * Real.exp ((|Γ| + 4 / 3 * Λ2 * t) / 2 ^ (k + 1)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          calc Real.exp (4 / 3 * Λ2 * t / 2 ^ (k + 1)) *
                (Real.sqrt A0 * Real.exp (Γ / 2 + κ + |Γ| / 2 ^ (k + 1)))
              = Real.sqrt A0 * (Real.exp (4 / 3 * Λ2 * t / 2 ^ (k + 1)) *
                Real.exp (Γ / 2 + κ + |Γ| / 2 ^ (k + 1))) := by ring
            _ = _ := by rw [hx]; ring
  have hlim := le_of_forall_exp hfin
  have hA00 : 0 ≤ A0 := by
    rw [hA0]; exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun z => sq_nonneg _)
  calc F t y ^ 2 ≤ (Real.sqrt A0 * Real.exp (Γ / 2 + κ)) ^ 2 :=
        pow_le_pow_left₀ (hFt0 y) hlim 2
    _ = A0 * Real.exp (Γ + 2 * κ) := by
        rw [mul_pow, Real.sq_sqrt hA00, ← Real.exp_nat_mul]
        congr 2; push_cast; ring

end Sup

end MarkovHK.H5Core

namespace CarlenKusuokaStroock

open MarkovHK.H5Core CarlenKusuokaStroock.H5

/-- **`CoreL2` holds** (with `C₃ = 16^{1/β} (C/β)^{1/β}` and the exponent
`δs + (26/3)Λ(ψ)²s ≤ 2δs + 72Λ(ψ)²s`). -/
theorem coreL2 : CoreL2.{u} := by
  intro C β hC hβ
  refine ⟨16 ^ (1 / β) * (C / β) ^ (1 / β), by positivity, ?_⟩
  intro X _ _ J ρ φR R hJ hJs hρ hφR hN ψ hψb hD s hs y
  classical
  set K := nearPart J ρ R with hKd
  have hK0 : ∀ x y, 0 ≤ K x y := nearPart_nonneg hJ R
  have hKr : ∀ x, Summable (K x) := summable_nearPart hJ R
  have hK1 : ∀ x, ∑' y, K x y ≤ 1 := tsum_nearPart_le hJ R
  have hKs : IsSymmetric K := nearPart_symm hJs hρ R
  set U := uniformize K with hUd
  have hU : IsTransition U := isTransition_uniformize hK0 hKr hK1
  have hUs : IsSymmetric U := uniformize_symm hKs
  obtain ⟨M, hM⟩ := hψb
  set φ : X → ℝ := fun z => -ψ z with hφ
  have hMφ : ∀ z, |φ z| ≤ M := fun z => by simp only [hφ, abs_neg]; exact hM z
  have hDn : daviesSq K φ = daviesSq K ψ := daviesSq_neg K ψ
  set Λ2 := (daviesSq K ψ).toReal with hΛ2
  have hΛ0 : 0 ≤ Λ2 := ENNReal.toReal_nonneg
  have hΛ : ∀ z, ∑' w, uniformize K z w * dw φ z w ≤ 2 * Λ2 := by
    intro z
    have := davies_bound hK0 hKr hMφ (by rw [hDn]; exact hD) z
    rwa [hDn] at this
  set δ := 4 / φR R with hδd
  have hδ : 0 ≤ δ := by positivity
  -- the column
  set a : X → ℝ := fun z => Real.exp (-ψ z) * heatKernel K s z y * Real.exp (ψ y) with ha
  have hhk : ∀ z w, heatKernel K s z w = hk U s z w := fun z w => rfl
  have ha0 : ∀ z, 0 ≤ a z := fun z => by
    simp only [ha, hhk]; have := hk_nonneg hU hs.le z y; positivity
  set Q := 16 ^ (1 / β) * (C / β) ^ (1 / β) * s ^ (-1 / β) *
    Real.exp (2 * (4 / φR R) * s + 72 * (daviesSq K ψ).toReal * s) with hQ
  -- the bound on finite pieces
  have hfin : ∀ F : Finset X, ∑ z ∈ F, a z ^ 2 ≤ Q := by
    intro F
    set f : X → ℝ := fun z => if z ∈ F then a z else 0 with hf
    have hf0 : ∀ z, 0 ≤ f z := fun z => by simp only [hf]; split_ifs; exacts [ha0 z, le_rfl]
    have hfS : ∀ z, z ∉ F → f z = 0 := fun z hz => by simp [hf, hz]
    have hsup := sup_bound hK0 hKr hK1 hKs hMφ F hf0 hfS hΛ0 hΛ hC hβ hδ hN hs y
    set N := ∑ z ∈ F, a z ^ 2 with hNd
    have hN2 : ∑' z, f z ^ 2 = N := by
      rw [tsum_eq_sum (s := F) (fun z hz => by simp [hf, hz])]
      exact Finset.sum_congr rfl fun z hz => by simp [hf, hz]
    have htraj : traj U φ F f s y = N := by
      unfold traj
      refine Finset.sum_congr rfl fun w hw => ?_
      have hsym : hk U s y w = hk U s w y := by
        rw [← hk_eq_heat hU, ← hk_eq_heat hU, heat_symm hU hUs]
      simp only [hf, hw, if_true, ha, hφ]
      rw [hsym, show heatKernel K s w y = hk U s w y from rfl]
      have e : Real.exp (-ψ w - -ψ y) = Real.exp (-ψ w) * Real.exp (ψ y) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]; ring
    rw [htraj, hN2] at hsup
    set W := Real.exp (4 * Λ2 * (2 * s / 3)) *
      Real.exp ((δ * s + 6 * Λ2 * s + (1 / β) * Real.log (C / (β * s))) + 2 * (Real.log 4 / β))
      with hW
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun z _ => sq_nonneg _
    have hNW : N ≤ W := by
      rcases hN0.eq_or_lt with h0 | hpos
      · rw [← h0]; positivity
      · have : N * N ≤ N * W := by
          rw [← sq]; refine hsup.trans (le_of_eq ?_); rw [hW]; ring
        exact le_of_mul_le_mul_left this hpos
    refine hNW.trans ?_
    have hlog : Real.exp ((1 / β) * Real.log (C / (β * s)) + 2 * (Real.log 4 / β)) =
        16 ^ (1 / β) * (C / β) ^ (1 / β) * s ^ (-1 / β) := by
      rw [Real.exp_add, mul_comm (1 / β), ← Real.rpow_def_of_pos (by positivity)]
      have h16 : Real.exp (2 * (Real.log 4 / β)) = 16 ^ (1 / β) := by
        rw [Real.rpow_def_of_pos (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
        congr 1; push_cast; ring
      rw [h16, show C / (β * s) = C / β / s by rw [div_div],
        Real.div_rpow (by positivity) hs.le, neg_div, Real.rpow_neg hs.le]
      ring
    have e : W = Real.exp (4 * Λ2 * (2 * s / 3) + δ * s + 6 * Λ2 * s) *
        Real.exp ((1 / β) * Real.log (C / (β * s)) + 2 * (Real.log 4 / β)) := by
      rw [hW, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e, hlog, hQ]
    have hle : Real.exp (4 * Λ2 * (2 * s / 3) + δ * s + 6 * Λ2 * s) ≤
        Real.exp (2 * (4 / φR R) * s + 72 * (daviesSq K ψ).toReal * s) := by
      refine Real.exp_le_exp.mpr ?_
      rw [← hΛ2, ← hδd]
      have : 0 ≤ δ * s := mul_nonneg hδ hs.le
      have : 0 ≤ Λ2 * s := mul_nonneg hΛ0 hs.le
      nlinarith
    have hpos : 0 ≤ 16 ^ (1 / β) * (C / β) ^ (1 / β) * s ^ (-1 / β) := by positivity
    calc Real.exp (4 * Λ2 * (2 * s / 3) + δ * s + 6 * Λ2 * s) *
          (16 ^ (1 / β) * (C / β) ^ (1 / β) * s ^ (-1 / β))
        ≤ Real.exp (2 * (4 / φR R) * s + 72 * (daviesSq K ψ).toReal * s) *
          (16 ^ (1 / β) * (C / β) ^ (1 / β) * s ^ (-1 / β)) :=
          mul_le_mul_of_nonneg_right hle hpos
      _ = _ := by ring
  have hsum : Summable (fun z => a z ^ 2) := summable_of_sum_le (fun z => sq_nonneg _) hfin
  exact hsum.tsum_le_of_sum_le hfin

end CarlenKusuokaStroock
end

section
/-!
# H5 (Carlen–Kusuoka–Stroock, Theorem 3.25), proved

`heatKernel_le_exp_davies_of_core` (`H5Red`: clamping to bounded `ψ`, the semigroup law at `t/2`,
Cauchy–Schwarz) applied to `coreL2` (`H5Core`: the CKS `L^{2^{k+1}}` iteration for the twisted
semigroup, `H5CoreAlg` … `H5CoreIter`).
-/


open DurrettProbability MarkovChain

namespace CarlenKusuokaStroock

end CarlenKusuokaStroock
end

section
open DurrettProbability MarkovChain
open CarlenKusuokaStroock
theorem solution (C β : ℝ) (hC : 0 < C) (hβ : 0 < β) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J ρ : X → X → ℝ)
      (φ : ℝ → ℝ) (R : ℝ),
      IsTransition J → IsSymmetric J → IsMetric ρ → 0 < φ R →
      SatisfiesNash (nearPart J ρ R) C (4 / φ R) β →
      ∀ ψ : X → ℝ, daviesSq (nearPart J ρ R) ψ ≠ ⊤ → ∀ t : ℝ, 0 < t → ∀ x y,
        heatKernel (nearPart J ρ R) t x y ≤
          C₂ * t ^ (-1 / β) *
            Real.exp (4 * t / φ R + 72 * (daviesSq (nearPart J ρ R) ψ).toReal * t - ψ y + ψ x) :=
  heatKernel_le_exp_davies_of_core coreL2 C β hC hβ
end
