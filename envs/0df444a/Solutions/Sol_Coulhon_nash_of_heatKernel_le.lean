-- Prove2me | solution 1 for Coulhon.nash_of_heatKernel_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:42:10.316982+00:00
-- url     : https://prove2.me/submissions/75f0948e-6631-4dea-8c8e-b8dc3beed492

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

/-- Rows of powers of a transition kernel sum to one. -/
lemma tsum_stepProb {p : X → X → ℝ} (hp : IsTransition p) (n : ℕ) (x : X) :
    ∑' y, stepProb p n x y = 1 := by
  induction n generalizing x with
  | zero =>
    have : (fun y => stepProb p 0 x y) = fun y => if y = x then 1 else 0 := by
      funext y; simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
    rw [this, tsum_ite_eq]
  | succ n ih =>
    have hs := isSub_of_isTransition hp
    have h := tsum_comm_triple (hs.1 x) (hs.2.1 x) (isSub_stepProb hs n) (r := fun _ => 1)
      (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one, ih] at h
    simp only [stepProb_succ]
    rw [← h, hp.2.2 x]

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

lemma summable_stepProb_col {p : X → X → ℝ} (hp : IsTransition p) (hs : IsSymmetric p) (n : ℕ)
    (y : X) : Summable (fun z => stepProb p n z y) :=
  ((isSub_stepProb (isSub_of_isTransition hp) n).2.1 y).congr fun z =>
    stepProb_symm (isSub_of_isTransition hp) hs n y z

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

variable {X : Type*} [DecidableEq X]

lemma heat_nonneg {J : X → X → ℝ} (hJ : IsTransition J) {t : ℝ} (ht : 0 ≤ t) (u v : X) :
    0 ≤ heatKernel J t u v := by
  rw [heatKernel_eq, uniformize_eq_self hJ]
  exact tsum_nonneg fun n => mul_nonneg (poi_nonneg ht n)
    (stepProb_nonneg (isSub_of_isTransition hJ) n u v)

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

end MarkovHK
end

section
/-!
# Moments `⟨Uⁿ f, f⟩` of a symmetric transition kernel, without the spectral theorem

For `f` supported in a finite set `S`: `gₐ = Uᵃ f` and `mₙ = ⟨Uⁿ f, f⟩`.
* `mom_add`: `m_{a+b} = ⟨gₐ, g_b⟩`;
* `gv_succ`: `g_{a+1} = U gₐ`;
* `contraction`: `‖U h‖₂ ≤ ‖h‖₂` (Jensen and unit column sums);
* `mom_sub_le`: `m₀ − mₙ ≤ n (m₀ − m₁)`, from `m_i − m_{i+1} ≤ m₀ − m₁`.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

/-- Jensen for sub-probability weights: `(∑ u v)² ≤ ∑ u v²` when `∑ u ≤ 1`. -/
lemma sq_tsum_le {u v : X → ℝ} (hu0 : ∀ w, 0 ≤ u w) (hus : Summable u) (hu1 : ∑' w, u w ≤ 1)
    (huv : Summable (fun w => u w * v w)) (huv2 : Summable (fun w => u w * v w ^ 2)) :
    (∑' w, u w * v w) ^ 2 ≤ ∑' w, u w * v w ^ 2 := by
  set c := ∑' w, u w * v w with hc
  have hexp : ∀ w, u w * (v w - c) ^ 2 = u w * v w ^ 2 - 2 * c * (u w * v w) + c ^ 2 * u w := by
    intro w; ring
  have hs : Summable (fun w => u w * v w ^ 2 - 2 * c * (u w * v w) + c ^ 2 * u w) :=
    (huv2.sub (huv.mul_left (2 * c))).add (hus.mul_left (c ^ 2))
  have h0 : 0 ≤ ∑' w, (u w * v w ^ 2 - 2 * c * (u w * v w) + c ^ 2 * u w) :=
    tsum_nonneg fun w => by rw [← hexp]; exact mul_nonneg (hu0 w) (sq_nonneg _)
  rw [(huv2.sub (huv.mul_left (2 * c))).tsum_add (hus.mul_left (c ^ 2)),
    huv2.tsum_sub (huv.mul_left (2 * c)), tsum_mul_left, tsum_mul_left, ← hc] at h0
  have : c ^ 2 * ∑' w, u w ≤ c ^ 2 := by
    calc c ^ 2 * ∑' w, u w ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left hu1 (sq_nonneg c)
      _ = c ^ 2 := mul_one _
  nlinarith

variable [DecidableEq X]

/-- `‖U h‖₂² ≤ ‖h‖₂²` for a symmetric transition kernel `U`. -/
lemma contraction {U : X → X → ℝ} (hU : IsTransition U) (hUs : IsSymmetric U) {h : X → ℝ}
    (hh : Summable (fun w => h w ^ 2)) :
    (∀ z, Summable (fun w => U z w * h w)) ∧ Summable (fun z => (∑' w, U z w * h w) ^ 2) ∧
      ∑' z, (∑' w, U z w * h w) ^ 2 ≤ ∑' w, h w ^ 2 := by
  have hUS := isSub_of_isTransition hU
  have hrow1 : ∀ z, Summable (fun w => U z w * h w) := fun z =>
    Summable.of_norm_bounded (g := fun w => (U z w + h w ^ 2) / 2)
      (((hU.2.1 z).add hh).div_const 2) (fun w => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU.1 z w)]
        have h1 := hU.1 z w
        have h2 := hUS.le_one z w
        nlinarith [sq_nonneg (|h w| - 1), sq_abs (h w), abs_nonneg (h w)])
  have hrow2 : ∀ z, Summable (fun w => U z w * h w ^ 2) := fun z =>
    Summable.of_nonneg_of_le (fun w => mul_nonneg (hU.1 z w) (sq_nonneg _))
      (fun w => by
        have := mul_le_mul_of_nonneg_right (hUS.le_one z w) (sq_nonneg (h w))
        simpa using this) hh
  -- `∑_z ∑_w U(z,w) h(w)² = ∑_w h(w)²`
  have hcol := summable_col (fun w => sq_nonneg (h w)) hh hUS
  have hfub := tsum_comm_triple (fun w => sq_nonneg (h w)) hh hUS (r := fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl)
  simp only [mul_one, hU.2.2] at hfub
  have hswap : ∀ z, ∑' w, h w ^ 2 * U w z = ∑' w, U z w * h w ^ 2 := fun z =>
    tsum_congr fun w => by rw [hUs w z]; ring
  have hjen : ∀ z, (∑' w, U z w * h w) ^ 2 ≤ ∑' w, U z w * h w ^ 2 := fun z =>
    sq_tsum_le (hU.1 z) (hU.2.1 z) (hU.2.2 z).le (hrow1 z) (hrow2 z)
  have hsum2 : Summable (fun z => ∑' w, U z w * h w ^ 2) := hcol.1.congr hswap
  refine ⟨hrow1, Summable.of_nonneg_of_le (fun z => sq_nonneg _) hjen hsum2, ?_⟩
  calc ∑' z, (∑' w, U z w * h w) ^ 2 ≤ ∑' z, ∑' w, U z w * h w ^ 2 :=
        Summable.tsum_le_tsum hjen (Summable.of_nonneg_of_le (fun z => sq_nonneg _) hjen hsum2)
          hsum2
    _ = ∑' w, h w ^ 2 := by
        rw [← tsum_congr hswap, ← hfub]

/-- `mₙ = ⟨Uⁿ f, f⟩` for `f` supported in `S`. -/
noncomputable def mom (U : X → X → ℝ) (S : Finset X) (f : X → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, f x * stepProb U n x y * f y

/-- `gₐ = Uᵃ f`. -/
noncomputable def gv (U : X → X → ℝ) (S : Finset X) (f : X → ℝ) (a : ℕ) (z : X) : ℝ :=
  ∑ x ∈ S, stepProb U a z x * f x

section Moments

variable {U : X → X → ℝ} (hU : IsTransition U) (hUs : IsSymmetric U) (S : Finset X) (f : X → ℝ)
include hU hUs

lemma abs_gv_le_sum (a : ℕ) (z : X) : |gv U S f a z| ≤ ∑ x ∈ S, stepProb U a z x * |f x| := by
  have hUS := isSub_of_isTransition hU
  unfold gv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul, abs_of_nonneg (stepProb_nonneg hUS a z x)]

lemma abs_gv_le (a : ℕ) (z : X) : |gv U S f a z| ≤ ∑ x ∈ S, |f x| := by
  have hUS := isSub_of_isTransition hU
  refine (abs_gv_le_sum hU hUs S f a z).trans (Finset.sum_le_sum fun x _ => ?_)
  have := mul_le_mul_of_nonneg_right (stepProb_le_one hUS a z x) (abs_nonneg (f x))
  simpa using this

lemma summable_abs_gv (a : ℕ) : Summable (fun z => |gv U S f a z|) := by
  refine Summable.of_nonneg_of_le (fun z => abs_nonneg _) (abs_gv_le_sum hU hUs S f a) ?_
  exact summable_sum fun x _ => (summable_stepProb_col hU hUs a x).mul_right _

lemma summable_gv_mul (a b : ℕ) : Summable (fun z => gv U S f a z * gv U S f b z) := by
  refine Summable.of_norm_bounded (g := fun z => (∑ x ∈ S, |f x|) * |gv U S f b z|)
    ((summable_abs_gv hU hUs S f b).mul_left _) (fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_gv_le hU hUs S f a z) (abs_nonneg _)

lemma summable_gv_sq (a : ℕ) : Summable (fun z => gv U S f a z ^ 2) :=
  (summable_gv_mul hU hUs S f a a).congr fun z => by ring

/-- `m_{a+b} = ⟨gₐ, g_b⟩`. -/
lemma mom_add (a b : ℕ) : mom U S f (a + b) = ∑' z, gv U S f a z * gv U S f b z := by
  have hUS := isSub_of_isTransition hU
  have hsum : ∀ x y, Summable (fun z => stepProb U a x z * stepProb U b z y) := fun x y =>
    Summable.of_nonneg_of_le (fun z => mul_nonneg (stepProb_nonneg hUS a x z)
      (stepProb_nonneg hUS b z y)) (fun z => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hUS b z y) (stepProb_nonneg hUS a x z)
        simpa using this) ((isSub_stepProb hUS a).2.1 x)
  unfold mom gv
  simp only [stepProb_add hUS a b]
  have e1 : ∀ x y, f x * (∑' z, stepProb U a x z * stepProb U b z y) * f y =
      ∑' z, f x * (stepProb U a x z * stepProb U b z y) * f y := by
    intro x y; rw [← tsum_mul_left, ← tsum_mul_right]
  simp only [e1]
  rw [Finset.sum_congr rfl fun x _ => (Summable.tsum_finsetSum fun y _ =>
    ((hsum x y).mul_left (f x)).mul_right (f y)).symm]
  rw [(Summable.tsum_finsetSum fun x _ => summable_sum fun y _ =>
    ((hsum x y).mul_left (f x)).mul_right (f y)).symm]
  refine tsum_congr fun z => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [stepProb_symm hUS hUs a x z]; ring

/-- `g_{a+1} = U gₐ`. -/
lemma gv_succ (a : ℕ) (z : X) : gv U S f (a + 1) z = ∑' w, U z w * gv U S f a w := by
  have hUS := isSub_of_isTransition hU
  unfold gv
  simp only [stepProb_succ]
  have hs : ∀ x, Summable (fun w => U z w * stepProb U a w x * f x) := fun x =>
    (Summable.of_nonneg_of_le (fun w => mul_nonneg (hU.1 z w) (stepProb_nonneg hUS a w x))
      (fun w => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hUS a w x) (hU.1 z w)
        simpa using this) (hU.2.1 z)).mul_right (f x)
  rw [Finset.sum_congr rfl fun x _ => (tsum_mul_right (f := fun w => U z w * stepProb U a w x)
    (a := f x)).symm, (Summable.tsum_finsetSum fun x _ => hs x).symm]
  refine tsum_congr fun w => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Gram: `‖gₐ − g_b‖² = m_{2a} − 2 m_{a+b} + m_{2b}`. -/
lemma gram (a b : ℕ) :
    ∑' z, (gv U S f a z - gv U S f b z) ^ 2 = mom U S f (a + a) - 2 * mom U S f (a + b) +
      mom U S f (b + b) := by
  rw [mom_add hU hUs, mom_add hU hUs, mom_add hU hUs]
  have e : ∀ z, (gv U S f a z - gv U S f b z) ^ 2 = gv U S f a z * gv U S f a z -
      2 * (gv U S f a z * gv U S f b z) + gv U S f b z * gv U S f b z := fun z => by ring
  simp only [e]
  rw [((summable_gv_mul hU hUs S f a a).sub ((summable_gv_mul hU hUs S f a b).mul_left 2)).tsum_add
    (summable_gv_mul hU hUs S f b b), (summable_gv_mul hU hUs S f a a).tsum_sub
    ((summable_gv_mul hU hUs S f a b).mul_left 2), tsum_mul_left]

lemma gram_nonneg (a b : ℕ) :
    0 ≤ mom U S f (a + a) - 2 * mom U S f (a + b) + mom U S f (b + b) := by
  rw [← gram hU hUs]; exact tsum_nonneg fun z => sq_nonneg _

/-- The contraction step `‖g_{j+1} − g_{j+2}‖² ≤ ‖g_j − g_{j+1}‖²`. -/
lemma gram_contract (j : ℕ) :
    mom U S f ((j + 1) + (j + 1)) - 2 * mom U S f ((j + 1) + (j + 2)) + mom U S f ((j + 2) + (j + 2))
      ≤ mom U S f (j + j) - 2 * mom U S f (j + (j + 1)) + mom U S f ((j + 1) + (j + 1)) := by
  rw [← gram hU hUs, ← gram hU hUs]
  set h : X → ℝ := fun w => gv U S f j w - gv U S f (j + 1) w with hh
  have hhs : Summable (fun w => h w ^ 2) := by
    have := gram hU hUs S f j (j + 1)
    by_contra hns
    have : ∑' w, h w ^ 2 = 0 := tsum_eq_zero_of_not_summable hns
    -- summable anyway: dominated by `2 g_j² + 2 g_{j+1}²`
    exact hns (Summable.of_nonneg_of_le (fun w => sq_nonneg _) (fun w => by
      simp only [hh]; nlinarith [sq_nonneg (gv U S f j w + gv U S f (j + 1) w)])
      (((summable_gv_sq hU hUs S f j).mul_left 2).add ((summable_gv_sq hU hUs S f (j + 1)).mul_left 2)))
  obtain ⟨hr1, _, hle⟩ := contraction hU hUs hhs
  have hUh : ∀ z, ∑' w, U z w * h w = gv U S f (j + 1) z - gv U S f (j + 2) z := by
    intro z
    rw [gv_succ hU hUs S f j z, gv_succ hU hUs S f (j + 1) z]
    have hs1 : Summable (fun w => U z w * gv U S f j w) := by
      have := (contraction hU hUs (summable_gv_sq hU hUs S f j)).1 z; exact this
    have hs2 : Summable (fun w => U z w * gv U S f (j + 1) w) := by
      have := (contraction hU hUs (summable_gv_sq hU hUs S f (j + 1))).1 z; exact this
    rw [← hs1.tsum_sub hs2]
    exact tsum_congr fun w => by simp only [hh]; ring
  simp only [hUh] at hle
  exact hle

/-- `m_i − m_{i+1} ≤ m₀ − m₁`. -/
lemma mom_diff_le (i : ℕ) :
    mom U S f i - mom U S f (i + 1) ≤ mom U S f 0 - mom U S f 1 := by
  -- even steps decrease
  have heven : ∀ j, mom U S f (2 * j) - mom U S f (2 * j + 1) ≤ mom U S f 0 - mom U S f 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      -- `d_{2j+2} ≤ d_{2j}`: (P+) = ‖h‖² + ⟨h, U h⟩ ≥ (‖h‖² − ‖U h‖²)/2 ≥ 0
      have hc := gram_contract hU hUs S f j
      have hg := gram_nonneg hU hUs S f j (j + 2)
      have e1 : j + 1 + (j + 1) = 2 * j + 2 := by ring
      have e2 : j + 1 + (j + 2) = 2 * j + 3 := by ring
      have e3 : j + 2 + (j + 2) = 2 * j + 4 := by ring
      have e4 : j + j = 2 * j := by ring
      have e5 : j + (j + 1) = 2 * j + 1 := by ring
      have e6 : j + (j + 2) = 2 * j + 2 := by ring
      rw [e1, e2, e3, e4, e5] at hc
      rw [e4, e6, e3] at hg
      have e7 : 2 * (j + 1) = 2 * j + 2 := by ring
      rw [e7]
      linarith
  rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by ring]; exact heven j
  · -- `d_{2j+1} ≤ d_{2j}` by Gram
    have hg := gram_nonneg hU hUs S f j (j + 1)
    rw [show j + j = 2 * j by ring, show j + (j + 1) = 2 * j + 1 by ring,
      show j + 1 + (j + 1) = 2 * j + 2 by ring] at hg
    have := heven j
    rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring]
    linarith

/-- `m₀ − mₙ ≤ n (m₀ − m₁)`. -/
lemma mom_sub_le (n : ℕ) : mom U S f 0 - mom U S f n ≤ n * (mom U S f 0 - mom U S f 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := mom_diff_le hU hUs S f n
    push_cast
    linarith

end Moments

end MarkovHK
end

section
/-!
# H4: ultracontractivity gives a Nash inequality (Coulhon, Proposition II.2)

For finitely supported `f` (support `S`), `U = uniformize J^R_1`, `δ = 4/φ(R)`, `N = ‖f‖₂²`,
`L = ‖f‖₁`, `E = ℰ(f)` and `Q_s = ⟨P_s f, f⟩ = ∑ₙ poi(s, n) mₙ`:
* `E = m₀ − m₁` (`dirichlet_eq_mom`), so `N − Q_s ≤ s E` by `mom_sub_le`;
* `Q_s ≤ N` (rows of the heat kernel sum to one) and `Q_s ≤ C e^{δs} s^{−1/β} L²`;
* hence `N ≤ s (E + δ N) + C s^{−1/β} L²` for every `s > 0`; take `s = (2 C L²/N)^β`:
  `N^{1+β} ≤ 2 (2C)^β (E + δ N) L^{2β}`.
-/


open DurrettProbability MarkovChain MarkovHK

namespace Coulhon

namespace H4

variable {X : Type*}

/-- A function on `X × X` vanishing off `Ω × X`, with summable rows, is summable, and its sum is
the finite sum of its row sums. -/
lemma summable_prod_of_rows (Ω : Finset X) (g : X × X → ℝ) (hg : ∀ p : X × X, p.1 ∉ Ω → g p = 0)
    (hrow : ∀ x, Summable (fun y => g (x, y))) :
    Summable g ∧ ∑' p, g p = ∑ x ∈ Ω, ∑' y, g (x, y) := by
  classical
  have hdecomp : g = fun p => ∑ x ∈ Ω, (if p.1 = x then g p else 0) := by
    funext p
    rw [Finset.sum_ite_eq]
    split_ifs with hp
    · rfl
    · exact hg p hp
  have hpiece : ∀ x, Summable (fun p : X × X => if p.1 = x then g p else 0) ∧
      ∑' p : X × X, (if p.1 = x then g p else 0) = ∑' y, g (x, y) := by
    intro x
    have hinj : Function.Injective (fun y : X => (x, y)) := fun a b h => (Prod.mk.inj h).2
    have hsupp : ∀ p ∉ Set.range (fun y : X => (x, y)), (if p.1 = x then g p else 0) = 0 := by
      intro p hp
      split_ifs with h
      · exact absurd ⟨p.2, by ext <;> simp [h]⟩ hp
      · rfl
    have hcomp : ((fun p : X × X => if p.1 = x then g p else 0) ∘ fun y => (x, y)) =
        fun y => g (x, y) := by
      funext y; simp
    refine ⟨(hinj.summable_iff hsupp).mp (by rw [hcomp]; exact hrow x), ?_⟩
    have := hinj.tsum_eq (f := fun p : X × X => if p.1 = x then g p else 0) (by
      intro p hp
      by_contra hc
      exact hp (hsupp p hc))
    rw [← this]
    simp
  constructor
  · rw [hdecomp]
    exact summable_sum fun x _ => (hpiece x).1
  · conv_lhs => rw [hdecomp]
    rw [Summable.tsum_finsetSum fun x _ => (hpiece x).1]
    exact Finset.sum_congr rfl fun x _ => (hpiece x).2


/-- The optimisation in `s` (Coulhon's choice). -/
lemma nash_opt {N E L C δ β : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E) (hL : 0 ≤ L) (hC : 0 < C) (hδ : 0 ≤ δ)
    (hβ : 0 < β) (hNL : 0 < N → 0 < L)
    (hK : ∀ s : ℝ, 0 < s → N ≤ s * (E + δ * N) + C * s ^ (-1 / β) * L ^ 2) :
    N ^ (1 + β) ≤ 2 * (2 * C) ^ β * (E + δ * N) * L ^ (2 * β) := by
  rcases hN.lt_or_eq with hNpos | hN0
  swap
  · rw [← hN0, Real.zero_rpow (by linarith)]
    positivity
  have hLpos := hNL hNpos
  set A := 2 * C * L ^ 2 / N with hA
  have hApos : 0 < A := by positivity
  set s := A ^ β with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos hApos β
  have hsinv : s ^ (-1 / β) = N / (2 * C * L ^ 2) := by
    rw [hs, ← Real.rpow_mul hApos.le, show β * (-1 / β) = -1 by field_simp, Real.rpow_neg_one,
      hA, inv_div]
  have h1 := hK s hspos
  rw [hsinv] at h1
  have h2 : C * (N / (2 * C * L ^ 2)) * L ^ 2 = N / 2 := by field_simp
  rw [h2] at h1
  have h3 : N ≤ 2 * s * (E + δ * N) := by linarith
  have hsA : s = (2 * C) ^ β * L ^ (2 * β) / N ^ β := by
    rw [hs, hA, Real.div_rpow (by positivity) hN, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast L 2, ← Real.rpow_mul hL]
    push_cast; ring_nf
  rw [hsA] at h3
  have hNb : 0 < N ^ β := Real.rpow_pos_of_pos hNpos β
  rw [Real.rpow_add hNpos, Real.rpow_one]
  have : N * N ^ β ≤ 2 * ((2 * C) ^ β * L ^ (2 * β) / N ^ β) * (E + δ * N) * N ^ β :=
    mul_le_mul_of_nonneg_right h3 hNb.le
  have e : 2 * ((2 * C) ^ β * L ^ (2 * β) / N ^ β) * (E + δ * N) * N ^ β =
      2 * (2 * C) ^ β * (E + δ * N) * L ^ (2 * β) := by field_simp
  linarith

variable [DecidableEq X]

/-- Rows of the heat kernel of a transition kernel sum to one. -/
lemma tsum_heat_row {U : X → X → ℝ} (hU : IsTransition U) {s : ℝ} (hs : 0 ≤ s) (x : X) :
    ∑' w, heatKernel U s x w = 1 := by
  have hS := isSub_of_isTransition hU
  have h := tsum_comm_gen (poi_nonneg hs) (summable_poi s) (q := fun n w => stepProb U n x w)
    (fun n w => stepProb_nonneg hS n x w) (fun n => (isSub_stepProb hS n).2.1 x)
    (fun n => (isSub_stepProb hS n).2.2 x) (r := fun _ => 1) (fun _ => zero_le_one)
    (fun _ => le_rfl)
  simp only [mul_one, tsum_stepProb hU] at h
  simp only [heatKernel_eq, uniformize_eq_self hU]
  rw [← h, tsum_poi]

/-- `ℰ_K(f) = m₀ − m₁` for `U = uniformize K`, `K` symmetric substochastic, `f` supported in `S`. -/
lemma dirichlet_eq_mom {K : X → X → ℝ} (hK0 : ∀ x y, 0 ≤ K x y) (hKs : ∀ x, Summable (K x))
    (hKsym : IsSymmetric K) (S : Finset X) (f : X → ℝ) (hf : ∀ x ∉ S, f x = 0) :
    dirichletForm K (fun _ => 1) f = mom (uniformize K) S f 0 - mom (uniformize K) S f 1 := by
  set r : X → ℝ := fun x => ∑' y, K x y with hr
  set G1 : X × X → ℝ := fun p => f p.1 ^ 2 * K p.1 p.2 with hG1
  set G3 : X × X → ℝ := fun p => f p.1 * f p.2 * K p.1 p.2 with hG3
  obtain ⟨hG1s, hG1t⟩ := summable_prod_of_rows S G1 (fun p hp => by simp [hG1, hf p.1 hp])
    (fun x => (hKs x).mul_left (f x ^ 2))
  have hrow3 : ∀ x, Summable (fun y => G3 (x, y)) := fun x =>
    summable_of_ne_finset_zero (s := S) fun y hy => by simp [hG3, hf y hy]
  obtain ⟨hG3s, hG3t⟩ := summable_prod_of_rows S G3 (fun p hp => by simp [hG3, hf p.1 hp]) hrow3
  have hG2s : Summable (G1 ∘ Prod.swap) := (Equiv.summable_iff (Equiv.prodComm X X)).mpr hG1s
  have hG2t : ∑' p, (G1 ∘ Prod.swap) p = ∑' p, G1 p := (Equiv.prodComm X X).tsum_eq G1
  have hsplit : (fun p : X × X => (f p.1 - f p.2) ^ 2 * K p.1 p.2 * 1) =
      fun p => G1 p + (G1 ∘ Prod.swap) p - 2 * G3 p := by
    funext p
    simp only [hG1, hG3, Function.comp, Prod.fst_swap, Prod.snd_swap, hKsym p.2 p.1]
    ring
  have hE : dirichletForm K (fun _ => 1) f =
      ∑ x ∈ S, f x ^ 2 * r x - ∑ x ∈ S, ∑ y ∈ S, f x * f y * K x y := by
    unfold dirichletForm
    rw [hsplit, (hG1s.add hG2s).tsum_sub (hG3s.mul_left 2), hG1s.tsum_add hG2s, hG2t,
      tsum_mul_left, hG1t, hG3t]
    have e1 : ∀ x ∈ S, ∑' y, G1 (x, y) = f x ^ 2 * r x := fun x _ => by
      simp only [hG1, hr]; rw [tsum_mul_left]
    have e3 : ∀ x ∈ S, ∑' y, G3 (x, y) = ∑ y ∈ S, f x * f y * K x y := fun x _ => by
      rw [tsum_eq_sum (s := S) fun y hy => by simp [hG3, hf y hy]]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e3]
    ring
  have hm0 : mom (uniformize K) S f 0 = ∑ x ∈ S, f x ^ 2 := by
    unfold mom
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_eq_single x]
    · simp [stepProb_zero]; ring
    · intro y _ hyx; simp [stepProb_zero, Ne.symm hyx]
    · intro hx'; exact absurd hx hx'
  have hm1 : mom (uniformize K) S f 1 =
      ∑ x ∈ S, ∑ y ∈ S, f x * f y * K x y + ∑ x ∈ S, f x ^ 2 * (1 - r x) := by
    unfold mom
    simp only [stepProb_one, uniformize]
    have e : ∀ x y, f x * (K x y + if x = y then 1 - ∑' z, K x z else 0) * f y =
        f x * f y * K x y + (if x = y then f x ^ 2 * (1 - r x) else 0) := by
      intro x y; split_ifs with h
      · subst h; simp only [hr]; ring
      · ring
    simp only [e, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_ite_eq S x]
    simp [hx]
  rw [hE, hm0, hm1]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  ring

end H4


end Coulhon
end

section
open DurrettProbability MarkovChain MarkovHK
open Coulhon
open H4 in
theorem solution (C β : ℝ) (hC : 0 < C) (hβ : 0 < β) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J ρ : X → X → ℝ)
      (φ : ℝ → ℝ) (R : ℝ),
      IsTransition J → IsSymmetric J → IsMetric ρ → 0 < φ R →
      (∀ t : ℝ, 0 < t → ∀ x y,
        heatKernel (nearPart J ρ R) t x y ≤ C * Real.exp (4 * t / φ R) * t ^ (-1 / β)) →
      SatisfiesNash (nearPart J ρ R) C' (4 / φ R) β := by
  refine ⟨2 * (2 * C) ^ β, by positivity, ?_⟩
  intro X _ _ J ρ φ R hJ hJs hρ hφR hheat f hfin
  set K := nearPart J ρ R with hK
  set U := uniformize K with hU
  have hUT : IsTransition U := isTransition_uniformize (nearPart_nonneg hJ R)
    (summable_nearPart hJ R) (tsum_nearPart_le hJ R)
  have hKsym : IsSymmetric K := nearPart_symm hJs hρ R
  have hUs : IsSymmetric U := uniformize_symm hKsym
  have hUS := isSub_of_isTransition hUT
  set S := hfin.toFinset with hS
  have hf : ∀ x ∉ S, f x = 0 := fun x hx => by
    simpa [hS, Set.Finite.mem_toFinset, Function.mem_support] using hx
  set δ := 4 / φ R with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set N := mom U S f 0 with hNdef
  set L := ∑ x ∈ S, |f x| with hLdef
  set E := dirichletForm K (fun _ => 1) f with hEdef
  have hNn : normSq (fun _ => 1) f = N := by
    unfold normSq
    rw [tsum_eq_sum (s := S) (fun x hx => by simp [hf x hx]), hNdef, mom]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_eq_single x]
    · simp [stepProb_zero]; ring
    · intro y _ hyx; simp [stepProb_zero, Ne.symm hyx]
    · intro hx'; exact absurd hx hx'
  have hLn : ∑' x, |f x| = L := tsum_eq_sum fun x hx => by simp [hf x hx]
  have hEm : E = mom U S f 0 - mom U S f 1 :=
    dirichlet_eq_mom (nearPart_nonneg hJ R) (summable_nearPart hJ R) hKsym S f hf
  have hN0 : 0 ≤ N := by
    rw [← hNn]; exact tsum_nonneg fun x => by positivity
  have hE0 : 0 ≤ E := by
    rw [hEdef]; unfold dirichletForm
    exact mul_nonneg (by norm_num) (tsum_nonneg fun p => mul_nonneg (mul_nonneg (sq_nonneg _)
      (nearPart_nonneg hJ R _ _)) zero_le_one)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun x _ => abs_nonneg _
  have hNL : 0 < N → 0 < L := by
    intro hNpos
    by_contra hL
    have hLz : L = 0 := le_antisymm (not_lt.mp hL) hL0
    have hz : ∀ x ∈ S, f x = 0 := fun x hx =>
      abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun x _ => abs_nonneg (f x)).mp hLz x hx)
    have : N = 0 := by
      rw [hNdef, mom]; exact Finset.sum_eq_zero fun x hx => by simp [hz x hx]
    linarith
  -- the quadratic form of the heat kernel
  have hpRU : ∀ s u v, heatKernel K s u v = heatKernel U s u v := by
    intro s u v; rw [heatKernel_eq, heatKernel_eq, uniformize_eq_self hUT]
  have hmom_le : ∀ n, |mom U S f n| ≤ L ^ 2 := by
    intro n
    unfold mom
    calc |∑ x ∈ S, ∑ y ∈ S, f x * stepProb U n x y * f y|
        ≤ ∑ x ∈ S, ∑ y ∈ S, |f x| * |f y| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (stepProb_nonneg hUS n x y)]
          have := stepProb_le_one hUS n x y
          have h1 := abs_nonneg (f x)
          have h2 := abs_nonneg (f y)
          nlinarith [mul_nonneg h1 h2]
      _ = L ^ 2 := by rw [hLdef, sq, Finset.sum_mul_sum]
  have hkey : ∀ s : ℝ, 0 < s → N ≤ s * (E + δ * N) + C * s ^ (-1 / β) * L ^ 2 := by
    intro s hs
    set Q := ∑ x ∈ S, ∑ y ∈ S, f x * heatKernel K s x y * f y with hQ
    -- (a) `Q = ∑ₙ poi(s, n) mₙ`
    have hsm : ∀ x y, Summable (fun n => f x * (poi s n * stepProb U n x y) * f y) := fun x y =>
      ((summable_heat hUS hs.le x y).mul_left (f x)).mul_right (f y)
    have hQa : Q = ∑' n, poi s n * mom U S f n := by
      rw [hQ]
      simp only [hpRU, heatKernel_eq, uniformize_eq_self hUT]
      have e : ∀ x y, f x * (∑' n, poi s n * stepProb U n x y) * f y =
          ∑' n, f x * (poi s n * stepProb U n x y) * f y := by
        intro x y; rw [← tsum_mul_left, ← tsum_mul_right]
      simp only [e]
      rw [Finset.sum_congr rfl fun x _ => (Summable.tsum_finsetSum fun y _ => hsm x y).symm,
        (Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hsm x y).symm]
      refine tsum_congr fun n => ?_
      unfold mom
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    -- (b) `N − Q ≤ s E`
    have hsmom : Summable (fun n => poi s n * mom U S f n) :=
      Summable.of_norm_bounded (g := fun n => poi s n * L ^ 2) ((summable_poi s).mul_right _)
        (fun n => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poi_nonneg hs.le n)]
          exact mul_le_mul_of_nonneg_left (hmom_le n) (poi_nonneg hs.le n))
    have hb : N - Q ≤ s * E := by
      rw [hQa, hEm]
      have h1 : N = ∑' n, poi s n * N := by rw [tsum_mul_right, tsum_poi, one_mul]
      rw [h1, ← ((summable_poi s).mul_right N).tsum_sub hsmom]
      calc ∑' n, (poi s n * N - poi s n * mom U S f n)
          ≤ ∑' n, poi s n * n * (mom U S f 0 - mom U S f 1) := by
            refine Summable.tsum_le_tsum (fun n => ?_) (((summable_poi s).mul_right N).sub hsmom)
              ((summable_poi_mul s).mul_right _)
            rw [← mul_sub, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mom_sub_le hUT hUs S f n) (poi_nonneg hs.le n)
        _ = s * (mom U S f 0 - mom U S f 1) := by
            rw [tsum_mul_right, (hasSum_poi_mul s).tsum_eq]
    -- (c) `Q ≤ N`
    have hc : Q ≤ N := by
      have hrow : ∀ x, ∑ y ∈ S, heatKernel U s x y ≤ 1 := fun x => by
        rw [← tsum_heat_row hUT hs.le x]
        exact (summable_heat_row hUT hs.le x).sum_le_tsum S (fun y _ => heat_nonneg hUT hs.le x y)
      have hcol : ∀ y, ∑ x ∈ S, heatKernel U s x y ≤ 1 := fun y => by
        rw [show ∑ x ∈ S, heatKernel U s x y = ∑ x ∈ S, heatKernel U s y x from
          Finset.sum_congr rfl fun x _ => heat_symm hUT hUs s x y]
        exact hrow y
      have hN' : N = ∑ x ∈ S, f x ^ 2 := by
        rw [← hNn]; unfold normSq
        rw [tsum_eq_sum (s := S) (fun x hx => by simp [hf x hx])]
        exact Finset.sum_congr rfl fun x _ => by ring
      calc Q = ∑ x ∈ S, ∑ y ∈ S, f x * heatKernel U s x y * f y := by
            rw [hQ]; simp only [hpRU]
        _ ≤ ∑ x ∈ S, ∑ y ∈ S, (f x ^ 2 + f y ^ 2) / 2 * heatKernel U s x y := by
            refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
            have := heat_nonneg hUT hs.le x y
            nlinarith [sq_nonneg (f x - f y), mul_nonneg this (sq_nonneg (f x - f y))]
        _ = (∑ x ∈ S, f x ^ 2 * ∑ y ∈ S, heatKernel U s x y +
              ∑ y ∈ S, f y ^ 2 * ∑ x ∈ S, heatKernel U s x y) / 2 := by
            have e1 : ∑ x ∈ S, f x ^ 2 * ∑ y ∈ S, heatKernel U s x y =
                ∑ x ∈ S, ∑ y ∈ S, f x ^ 2 * heatKernel U s x y := by simp only [Finset.mul_sum]
            have e2 : ∑ y ∈ S, f y ^ 2 * ∑ x ∈ S, heatKernel U s x y =
                ∑ x ∈ S, ∑ y ∈ S, f y ^ 2 * heatKernel U s x y := by
              simp only [Finset.mul_sum]; exact Finset.sum_comm
            rw [e1, e2, ← Finset.sum_add_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            exact Finset.sum_congr rfl fun y _ => by ring
        _ ≤ (∑ x ∈ S, f x ^ 2 * 1 + ∑ y ∈ S, f y ^ 2 * 1) / 2 := by
            gcongr with x _ y _
            · exact hrow x
            · exact hcol y
        _ = N := by rw [hN']; simp
    -- (d) `Q ≤ C e^{δs} s^{−1/β} L²`
    have hd : Q ≤ C * Real.exp (δ * s) * s ^ (-1 / β) * L ^ 2 := by
      have hM : ∀ x y, heatKernel K s x y ≤ C * Real.exp (δ * s) * s ^ (-1 / β) := by
        intro x y
        have := hheat s hs x y
        rwa [show 4 * s / φ R = δ * s by rw [hδ]; ring] at this
      calc Q ≤ ∑ x ∈ S, ∑ y ∈ S, |f x| * (C * Real.exp (δ * s) * s ^ (-1 / β)) * |f y| := by
            refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
            have h0 : 0 ≤ heatKernel K s x y := by rw [hpRU]; exact heat_nonneg hUT hs.le x y
            calc f x * heatKernel K s x y * f y ≤ |f x * heatKernel K s x y * f y| := le_abs_self _
              _ = |f x| * heatKernel K s x y * |f y| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg h0]
              _ ≤ |f x| * (C * Real.exp (δ * s) * s ^ (-1 / β)) * |f y| := by
                  gcongr; exact hM x y
        _ = C * Real.exp (δ * s) * s ^ (-1 / β) * L ^ 2 := by
            rw [hLdef, sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
    -- combine
    have hex : 0 < Real.exp (-(δ * s)) := Real.exp_pos _
    have hex1 : Real.exp (-(δ * s)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := mul_nonneg hδ0 hs.le; linarith)
    have hlin : 1 - Real.exp (-(δ * s)) ≤ δ * s := by linarith [Real.add_one_le_exp (-(δ * s))]
    have hmid : (1 - Real.exp (-(δ * s))) * Q ≤ δ * s * N := by
      rcases le_or_gt 0 Q with hQ0 | hQ0
      · calc (1 - Real.exp (-(δ * s))) * Q ≤ (1 - Real.exp (-(δ * s))) * N :=
              mul_le_mul_of_nonneg_left hc (by linarith)
          _ ≤ δ * s * N := mul_le_mul_of_nonneg_right hlin hN0
      · have : (1 - Real.exp (-(δ * s))) * Q ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) hQ0.le
        have : 0 ≤ δ * s * N := by positivity
        linarith
    have hlast : Real.exp (-(δ * s)) * Q ≤ C * s ^ (-1 / β) * L ^ 2 := by
      calc Real.exp (-(δ * s)) * Q ≤ Real.exp (-(δ * s)) *
            (C * Real.exp (δ * s) * s ^ (-1 / β) * L ^ 2) := mul_le_mul_of_nonneg_left hd hex.le
        _ = C * s ^ (-1 / β) * L ^ 2 * (Real.exp (-(δ * s)) * Real.exp (δ * s)) := by ring
        _ = C * s ^ (-1 / β) * L ^ 2 := by rw [← Real.exp_add]; simp
    nlinarith [hb, hmid, hlast]
  have := nash_opt hN0 hE0 hL0 hC hδ0 hβ hNL hkey
  rw [hNn, hLn]
  exact this
end
