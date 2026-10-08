-- Prove2me | solution 1 for ErschlerZheng.heatKernel_le_of_onDiagonal_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:42:10.291421+00:00
-- url     : https://prove2.me/submissions/806071ea-a8c9-4af2-a35e-c71f2e8db1c4

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
import Theorems.Thm_Coulhon_nash_of_heatKernel_le
import Theorems.Thm_CarlenKusuokaStroock_heatKernel_le_exp_davies
import Theorems.Thm_BarlowGrigoryanKumagai_heatKernel_le_heatKernel_nearPart_add
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

lemma farPart_nonneg {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (x y : X) :
    0 ≤ farPart J ρ R x y := by
  unfold farPart; split_ifs
  · exact hJ.1 x y
  · exact le_rfl

lemma near_add_far (J ρ : X → X → ℝ) (R : ℝ) (x y : X) :
    nearPart J ρ R x y + farPart J ρ R x y = J x y := by
  unfold nearPart farPart
  by_cases h : ρ x y ≤ R
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

lemma summable_nearPart {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (x : X) :
    Summable (nearPart J ρ R x) :=
  Summable.of_nonneg_of_le (nearPart_nonneg hJ R x) (nearPart_le hJ R x) (hJ.2.1 x)

lemma tsum_nearPart_le {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (x : X) :
    ∑' y, nearPart J ρ R x y ≤ 1 := by
  rw [← hJ.2.2 x]
  exact Summable.tsum_le_tsum (nearPart_le hJ R x) (summable_nearPart hJ R x) (hJ.2.1 x)

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

end MarkovHK
end

section
/-!
# Binomial and shifted-exponential identities (shared by H9 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

/-- One Pascal step of the binomial theorem, for a sequence `b`. -/
lemma binom_step (a : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) * a ^ (n + 1 - k) * b k =
      a * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b (k + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1)]
  have h1 : ∀ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℝ) * a ^ (n + 1 - (k + 1)) * b (k + 1) =
        (n.choose k : ℝ) * a ^ (n - k) * b (k + 1) +
          (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ', Nat.succ_sub_succ]; push_cast; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun k => (n.choose k : ℝ) * a ^ (n - k) * b k) n]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1)) n]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.sub_zero]
  rw [mul_add, Finset.mul_sum]
  have h2 : ∀ k ∈ Finset.range n, a * ((n.choose (k + 1) : ℝ) * a ^ (n - (k + 1)) * b (k + 1)) =
      (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1) := by
    intro k hk
    have : n - k = (n - (k + 1)) + 1 := by have := Finset.mem_range.mp hk; omega
    rw [this, pow_succ]; ring
  rw [Finset.sum_congr rfl h2]
  ring

/-- The shifted exponential series: `∑_j poi(t, j) C(j, k) α^{j−k} = poi(t, k) e^{αt}`. -/
lemma hasSum_shift (t α : ℝ) (k : ℕ) :
    HasSum (fun j => poi t j * (j.choose k : ℝ) * α ^ (j - k)) (poi t k * Real.exp (α * t)) := by
  have hexp := NormedSpace.expSeries_div_hasSum_exp (α * t)
  rw [← Real.exp_eq_exp_ℝ] at hexp
  have h := hexp.mul_left (poi t k)
  rw [← hasSum_nat_add_iff' k]
  have hz : ∑ i ∈ Finset.range k, poi t i * (i.choose k : ℝ) * α ^ (i - k) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]; simp
  rw [hz, sub_zero]
  have e : (fun m => poi t (m + k) * ((m + k).choose k : ℝ) * α ^ (m + k - k)) =
      fun m => poi t k * ((α * t) ^ m / m.factorial) := by
    funext m
    have hc : ((m + k).choose k : ℝ) * m.factorial * k.factorial = (m + k).factorial := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial m k
    have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hmkf : ((m + k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hch : ((m + k).choose k : ℝ) = (m + k).factorial / (m.factorial * k.factorial) := by
      rw [← hc]; field_simp
    unfold poi
    rw [Nat.add_sub_cancel, hch, mul_pow, pow_add]
    field_simp
  rw [e]; exact h

variable {X : Type*} [DecidableEq X]

lemma summable_ite (x : X) (c : ℝ) : Summable (fun z : X => if x = z then c else 0) :=
  (hasSum_ite_eq x c).summable.congr fun z => by split_ifs <;> simp_all [eq_comm]

lemma tsum_ite (x : X) (c : ℝ) : ∑' z : X, (if x = z then c else 0) = c := by
  rw [show (fun z : X => if x = z then c else 0) = fun z => if z = x then c else 0 by
    funext z; split_ifs <;> simp_all [eq_comm]]
  exact tsum_ite_eq x (fun _ => c)

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

lemma tsum_mul_le_avg {a b : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (hb0 : ∀ w, 0 ≤ b w)
    (ha1 : ∀ w, a w ≤ 1) (hb1 : ∀ w, b w ≤ 1) (has : Summable a) (hbs : Summable b) :
    ∑' w, a w * b w ≤ (∑' w, a w * a w + ∑' w, b w * b w) / 2 := by
  have hsq : ∀ (c : X → ℝ), (∀ w, 0 ≤ c w) → (∀ w, c w ≤ 1) → Summable c →
      Summable (fun w => c w * c w) := fun c h0 h1 hs =>
    Summable.of_nonneg_of_le (fun w => mul_nonneg (h0 w) (h0 w))
      (fun w => by have := mul_le_mul_of_nonneg_left (h1 w) (h0 w); simpa using this) hs
  have hab : Summable (fun w => a w * b w) :=
    Summable.of_nonneg_of_le (fun w => mul_nonneg (ha0 w) (hb0 w))
      (fun w => by have := mul_le_mul_of_nonneg_left (hb1 w) (ha0 w); simpa using this) has
  rw [← (hsq a ha0 ha1 has).tsum_add (hsq b hb0 hb1 hbs), ← tsum_div_const]
  refine Summable.tsum_le_tsum (fun w => ?_) hab
    (((hsq a ha0 ha1 has).add (hsq b hb0 hb1 hbs)).div_const 2)
  nlinarith [sq_nonneg (a w - b w)]

/-- Off the diagonal, by the semigroup law at `t/2`, symmetry and `ab ≤ (a² + b²)/2`. -/
lemma heat_le_avg_diag {J : X → X → ℝ} (hJ : IsTransition J) (hJs : IsSymmetric J) {t : ℝ}
    (ht : 0 ≤ t) (u v : X) :
    heatKernel J t u v ≤ (heatKernel J t u u + heatKernel J t v v) / 2 := by
  have h2 : 0 ≤ t / 2 := by linarith
  have htt : t / 2 + t / 2 = t := by ring
  have hsg := fun a b => heat_semigroup hJ h2 h2 a b
  rw [htt] at hsg
  rw [← hsg u v, ← hsg u u, ← hsg v v]
  have e1 : ∀ c d : X, (fun w => heatKernel J (t / 2) c w * heatKernel J (t / 2) w d) =
      fun w => heatKernel J (t / 2) c w * heatKernel J (t / 2) d w :=
    fun c d => funext fun w => by rw [heat_symm hJ hJs _ w d]
  rw [e1 u v, e1 u u, e1 v v]
  exact tsum_mul_le_avg (fun w => heat_nonneg hJ h2 u w) (fun w => heat_nonneg hJ h2 v w)
    (fun w => heat_le_one hJ h2 u w) (fun w => heat_le_one hJ h2 v w)
    (summable_heat_row hJ h2 u) (summable_heat_row hJ h2 v)

/-- Domination: if `A ≤ B + δ I` then `Aⁿ ≤ ∑_{k ≤ n} C(n, k) δ^{n−k} Bᵏ`. -/
lemma stepProb_le_binom {A B : X → X → ℝ} (hA : IsTransition A) (hB : IsTransition B) {δ : ℝ}
    (hδ : 0 ≤ δ) (hAB : ∀ x y, A x y ≤ B x y + if x = y then δ else 0) (n : ℕ) :
    ∀ x y, stepProb A n x y ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * δ ^ (n - k) * stepProb B k x y := by
  have hAS := isSub_of_isTransition hA
  have hBS := isSub_of_isTransition hB
  induction n with
  | zero => intro x y; simp [stepProb_zero]
  | succ n ih =>
    intro x y
    set E : X → ℝ := fun z =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * δ ^ (n - k) * stepProb B k z y with hE
    set M : ℝ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * δ ^ (n - k) with hM
    have hc0 : ∀ k, 0 ≤ (n.choose k : ℝ) * δ ^ (n - k) := fun k =>
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hδ _)
    have hE0 : ∀ z, 0 ≤ E z := fun z => Finset.sum_nonneg fun k _ =>
      mul_nonneg (hc0 k) (stepProb_nonneg hBS k z y)
    have hEM : ∀ z, E z ≤ M := fun z => Finset.sum_le_sum fun k _ => by
      have := mul_le_mul_of_nonneg_left (stepProb_le_one hBS k z y) (hc0 k)
      simpa using this
    have hs1 : Summable (fun z => A x z * stepProb A n z y) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hA.1 x z) (stepProb_nonneg hAS n z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hAS n z y) (hA.1 x z)
          simpa using this) (hA.2.1 x)
    have hs2 : Summable (fun z => A x z * E z) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hA.1 x z) (hE0 z))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (hEM z) (hA.1 x z)
          linarith [mul_comm (A x z) M]) ((hA.2.1 x).mul_right M)
    have hs3 : Summable (fun z => B x z * E z) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hB.1 x z) (hE0 z))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (hEM z) (hB.1 x z)
          linarith [mul_comm (B x z) M]) ((hB.2.1 x).mul_right M)
    have hs4 : ∀ k, Summable (fun z => B x z * stepProb B k z y) := fun k =>
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hB.1 x z) (stepProb_nonneg hBS k z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hBS k z y) (hB.1 x z)
          simpa using this) (hB.2.1 x)
    have hite := summable_ite (X := X) x (δ * E x)
    rw [stepProb_succ]
    calc ∑' z, A x z * stepProb A n z y
        ≤ ∑' z, (B x z * E z + if x = z then δ * E x else 0) := by
          refine Summable.tsum_le_tsum (fun z => ?_) hs1 (hs3.add hite)
          calc A x z * stepProb A n z y ≤ A x z * E z :=
                mul_le_mul_of_nonneg_left (ih z y) (hA.1 x z)
            _ ≤ (B x z + if x = z then δ else 0) * E z :=
                mul_le_mul_of_nonneg_right (hAB x z) (hE0 z)
            _ = B x z * E z + if x = z then δ * E x else 0 := by
                split_ifs with h
                · subst h; ring
                · ring
      _ = ∑' z, B x z * E z + δ * E x := by rw [hs3.tsum_add hite, tsum_ite]
      _ = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * δ ^ (n - k) *
            stepProb B (k + 1) x y + δ * E x := by
          congr 1
          simp only [hE, Finset.mul_sum]
          rw [Summable.tsum_finsetSum fun k _ => ((hs4 k).mul_left
            ((n.choose k : ℝ) * δ ^ (n - k))).congr fun z => by ring]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [stepProb_succ, ← tsum_mul_left]
          exact tsum_congr fun z => by ring
      _ = _ := by
          rw [binom_step δ (fun k => stepProb B k x y) n, hE]
          ring

/-- Comparison of heat kernels: `A ≤ B + δ I` gives `p_A(t) ≤ e^{δt} p_B(t)`. -/
lemma heat_le_exp_mul_heat {A B : X → X → ℝ} (hA : IsTransition A) (hB : IsTransition B) {δ : ℝ}
    (hδ : 0 ≤ δ) (hAB : ∀ x y, A x y ≤ B x y + if x = y then δ else 0) {t : ℝ} (ht : 0 ≤ t)
    (x y : X) : heatKernel A t x y ≤ Real.exp (δ * t) * heatKernel B t x y := by
  have hAS := isSub_of_isTransition hA
  have hBS := isSub_of_isTransition hB
  rw [heatKernel_eq, heatKernel_eq, uniformize_eq_self hA, uniformize_eq_self hB]
  set F : ℕ → ℕ → ℝ := fun k n => poi t n * (n.choose k : ℝ) * δ ^ (n - k) * stepProb B k x y
    with hF
  have hF0 : ∀ k n, 0 ≤ F k n := fun k n => mul_nonneg (mul_nonneg (mul_nonneg
    (poi_nonneg ht n) (Nat.cast_nonneg _)) (pow_nonneg hδ _)) (stepProb_nonneg hBS k x y)
  have hrow : ∀ k, HasSum (fun n => F k n) (poi t k * Real.exp (δ * t) * stepProb B k x y) :=
    fun k => (hasSum_shift t δ k).mul_right _
  have hFs : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
    refine (summable_prod_of_nonneg fun p => hF0 p.1 p.2).mpr ⟨fun k => (hrow k).summable, ?_⟩
    simp only [fun k => (hrow k).tsum_eq]
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (poi_nonneg ht k)
      (Real.exp_pos _).le) (stepProb_nonneg hBS k x y)) (fun k => ?_)
      ((summable_poi t).mul_right (Real.exp (δ * t)))
    have := mul_le_mul_of_nonneg_left (stepProb_le_one hBS k x y)
      (mul_nonneg (poi_nonneg ht k) (Real.exp_pos (δ * t)).le)
    simpa using this
  have hcol : ∀ n, ∑' k, F k n = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * δ ^ (n - k) * stepProb B k x y * poi t n := by
    intro n
    rw [tsum_eq_sum (s := Finset.range (n + 1)) fun k hk => ?_]
    · exact Finset.sum_congr rfl fun k _ => by simp only [hF]; ring
    · rw [Finset.mem_range, not_lt] at hk
      simp only [hF, Nat.choose_eq_zero_of_lt (by omega : n < k)]; simp
  calc ∑' n, poi t n * stepProb A n x y
      ≤ ∑' n, ∑' k, F k n := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_heat hAS ht x y)
          (by simpa using hFs.prod_symm.prod)
        rw [hcol, ← Finset.sum_mul, mul_comm _ (poi t n)]
        exact mul_le_mul_of_nonneg_left (stepProb_le_binom hA hB hδ hAB n x y) (poi_nonneg ht n)
    _ = ∑' k, ∑' n, F k n := Summable.tsum_comm (f := F) hFs
    _ = ∑' k, Real.exp (δ * t) * (poi t k * stepProb B k x y) :=
        tsum_congr fun k => by rw [(hrow k).tsum_eq]; ring
    _ = Real.exp (δ * t) * ∑' k, poi t k * stepProb B k x y := tsum_mul_left

end MarkovHK
end

section
/-!
# H8: Proposition 7.20 of Erschler–Zheng (pp. 49–52), from H4, H5 and H6

Following the printed proof, with two repairs.

1. `sup p_R(t) ≤ C₀ e^{4t/φ(R)} t^{−1/β}` (the hypothesis of H4): `uniformize J^R_1 ≤ J + I/φ(R)`
   (the far mass is at most `1/φ(R)`), so `p_R(t) ≤ e^{t/φ(R)} p(t)` (`heat_le_exp_mul_heat`), and
   `p(t, u, v) ≤ (p(t, u, u) + p(t, v, v))/2 ≤ C₀ t^{−1/β}` (`heat_le_avg_diag`).
2. The Davies function. The printed `ψ(z) = λ(ρ(z, x₀) − ρ(z, y₀))₊` is `2λ`-Lipschitz, not
   `λ`-Lipschitz as printed, and with `2λ` the printed choice of `λ` leaves an unbounded factor. We use
   `ψ(z) = λ(ρ(x₀, y₀) − ρ(z, y₀))₊`, which is `λ`-Lipschitz with the same values `ψ(x₀) = 0`,
   `ψ(y₀) = λρ(x₀, y₀)`; then `Λ(ψ)² ≤ λ² e^{2λR} R²/φ(R)` exactly as printed.
3. For `φ(R) ≤ t ≤ φ(ρ(x, y))` the printed `λ` is `≤ 0`; there `ψ = 0` and `t^{−1/β} ≤ t φ(R)^{−1−1/β}`.
-/


open DurrettProbability MarkovChain MarkovHK
open scoped ENNReal

namespace ErschlerZheng

namespace H8

/-- `(eˢ − 1)² ≤ s² e^{2|s|}`. -/
lemma exp_sub_one_sq_le (s : ℝ) : (Real.exp s - 1) ^ 2 ≤ s ^ 2 * Real.exp (2 * |s|) := by
  have key : |Real.exp s - 1| ≤ |s| * Real.exp |s| := by
    rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hs, abs_of_nonneg (by linarith [Real.add_one_le_exp s])]
      have h1 := Real.add_one_le_exp (-s)
      have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
      have h3 := Real.exp_pos s
      nlinarith
    · rw [abs_of_nonpos hs, abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr hs])]
      have h1 := Real.add_one_le_exp s
      have h2 : 1 ≤ Real.exp (-s) := Real.one_le_exp (by linarith)
      nlinarith
  have h0 : 0 ≤ |s| * Real.exp |s| := by positivity
  calc (Real.exp s - 1) ^ 2 = |Real.exp s - 1| ^ 2 := (sq_abs _).symm
    _ ≤ (|s| * Real.exp |s|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) key 2
    _ = s ^ 2 * Real.exp (2 * |s|) := by
        rw [mul_pow, sq_abs, ← Real.exp_nat_mul]; push_cast; ring_nf

variable {X : Type*}

/-- One half of `Λ(ψ)²`, for a kernel `K ≥ 0` and a function `g`. -/
lemma davies_half {K : X → X → ℝ} (hK0 : ∀ z w, 0 ≤ K z w) (g : X → ℝ) (z : X) {c : ℝ}
    (hc : 0 ≤ c) {B : X → ℝ} (hB0 : ∀ w, 0 ≤ B w) (hBs : Summable B)
    (hpt : ∀ w, (Real.exp (g w - g z) - 1) ^ 2 * K z w ≤ c * B w) :
    ENNReal.ofReal (Real.exp (-2 * g z)) * carreDuChamp K (fun w => Real.exp (g w)) z ≤
      ENNReal.ofReal (c * ∑' w, B w) := by
  unfold carreDuChamp
  rw [← ENNReal.tsum_mul_left]
  have hterm : ∀ w, ENNReal.ofReal (Real.exp (-2 * g z)) *
      ENNReal.ofReal ((Real.exp (g w) - Real.exp (g z)) ^ 2 * K z w) =
        ENNReal.ofReal ((Real.exp (g w - g z) - 1) ^ 2 * K z w) := by
    intro w
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    have e1 : Real.exp (-2 * g z) = Real.exp (-g z) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have e2 : Real.exp (g w - g z) = Real.exp (g w) * Real.exp (-g z) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (g z) * Real.exp (-g z) = 1 := by rw [← Real.exp_add]; simp
    rw [e1, e2]
    linear_combination K z w * (Real.exp (g z) * Real.exp (-g z) + 1 -
      2 * Real.exp (g w) * Real.exp (-g z)) * e3
  simp only [hterm]
  rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg hc (hB0 w))
    (hBs.mul_left c)]
  exact ENNReal.tsum_le_tsum fun w => ENNReal.ofReal_le_ofReal (hpt w)

/-- The Davies estimate for `ψ(z) = lam·(d − ρ(z, y₀))₊`, which is `lam`-Lipschitz:
`Λ(ψ)² ≤ lam² e^{2 lam R} M` when the truncated second moments are at most `M`. -/
lemma davies_bound {J ρ : X → X → ℝ} (hJ : IsTransition J) (hρ : IsMetric ρ) {R : ℝ}
    (hR : 0 ≤ R) {M : ℝ} (hmom : ∀ z, ∑' w, (if ρ z w ≤ R then ρ z w ^ 2 * J z w else 0) ≤ M)
    {lam : ℝ} (hlam : 0 ≤ lam) (d : ℝ) (y₀ : X) :
    daviesSq (nearPart J ρ R) (fun z => lam * max (d - ρ z y₀) 0) ≤
      ENNReal.ofReal (lam ^ 2 * Real.exp (2 * lam * R) * M) := by
  set ψ : X → ℝ := fun z => lam * max (d - ρ z y₀) 0 with hψ
  have hρ0 : ∀ z w, 0 ≤ ρ z w := fun z w => by
    have := hρ.triangle z w z; rw [hρ.self_eq z, hρ.symm w z] at this; linarith
  have hc : 0 ≤ lam ^ 2 * Real.exp (2 * lam * R) := by positivity
  set B : X → X → ℝ := fun z w => if ρ z w ≤ R then ρ z w ^ 2 * J z w else 0 with hBdef
  have hB0 : ∀ z w, 0 ≤ B z w := fun z w => by
    simp only [hBdef]; split_ifs
    · exact mul_nonneg (sq_nonneg _) (hJ.1 z w)
    · exact le_rfl
  have hBs : ∀ z, Summable (B z) := fun z =>
    Summable.of_nonneg_of_le (hB0 z) (fun w => by
      simp only [hBdef]; split_ifs with h
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hρ0 z w) h 2) (hJ.1 z w)
      · exact mul_nonneg (sq_nonneg R) (hJ.1 z w)) ((hJ.2.1 z).mul_left (R ^ 2))
  have hlip : ∀ z w, |ψ w - ψ z| ≤ lam * ρ z w := by
    intro z w
    simp only [hψ]
    rw [← mul_sub, abs_mul, abs_of_nonneg hlam]
    refine mul_le_mul_of_nonneg_left ?_ hlam
    calc |max (d - ρ w y₀) 0 - max (d - ρ z y₀) 0| ≤ |(d - ρ w y₀) - (d - ρ z y₀)| :=
          abs_max_sub_max_le_abs _ _ _
      _ = |ρ z y₀ - ρ w y₀| := by ring_nf
      _ ≤ ρ z w := by
          rw [abs_sub_le_iff]
          constructor
          · linarith [hρ.triangle z w y₀]
          · linarith [hρ.triangle w z y₀, hρ.symm z w]
  -- the pointwise bound, for `g = ±ψ`
  have hpt : ∀ g : X → ℝ, (∀ z w, |g w - g z| ≤ lam * ρ z w) → ∀ z w,
      (Real.exp (g w - g z) - 1) ^ 2 * nearPart J ρ R z w ≤
        lam ^ 2 * Real.exp (2 * lam * R) * B z w := by
    intro g hg z w
    simp only [hBdef, nearPart]
    split_ifs with h
    · have hs := hg z w
      have h1 := exp_sub_one_sq_le (g w - g z)
      have h2 : (g w - g z) ^ 2 ≤ lam ^ 2 * ρ z w ^ 2 := by
        rw [← sq_abs, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hs 2
      have h3 : Real.exp (2 * |g w - g z|) ≤ Real.exp (2 * lam * R) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left h hlam
        linarith
      have h4 : (Real.exp (g w - g z) - 1) ^ 2 ≤ lam ^ 2 * ρ z w ^ 2 * Real.exp (2 * lam * R) :=
        h1.trans (mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity))
      calc (Real.exp (g w - g z) - 1) ^ 2 * J z w
          ≤ lam ^ 2 * ρ z w ^ 2 * Real.exp (2 * lam * R) * J z w :=
            mul_le_mul_of_nonneg_right h4 (hJ.1 z w)
        _ = lam ^ 2 * Real.exp (2 * lam * R) * (ρ z w ^ 2 * J z w) := by ring
    · simp
  have hlip' : ∀ z w, |(fun z => -ψ z) w - (fun z => -ψ z) z| ≤ lam * ρ z w := by
    intro z w; simp only; rw [show -ψ w - -ψ z = -(ψ w - ψ z) by ring, abs_neg]; exact hlip z w
  have hK0 : ∀ z w, 0 ≤ nearPart J ρ R z w := nearPart_nonneg hJ R
  have hfinal : ∀ z, ENNReal.ofReal (lam ^ 2 * Real.exp (2 * lam * R) * ∑' w, B z w) ≤
      ENNReal.ofReal (lam ^ 2 * Real.exp (2 * lam * R) * M) := fun z =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hmom z) hc)
  unfold daviesSq
  refine max_le (iSup_le fun z => ?_) (iSup_le fun z => ?_)
  · exact (davies_half hK0 ψ z hc (hB0 z) (hBs z) (hpt ψ hlip z)).trans (hfinal z)
  · have h := davies_half hK0 (fun z => -ψ z) z hc (hB0 z) (hBs z) (hpt _ hlip' z)
    have e : Real.exp (-2 * (fun z => -ψ z) z) = Real.exp (2 * ψ z) := by
      simp only; ring_nf
    rw [e] at h
    exact h.trans (hfinal z)

/-- `t^{−1/β} (t/φ_R)^{1+1/β} ≤ Q^{1+1/β} t / φ_d^{1+1/β}` when `φ_d ≤ Q φ_R`. -/
lemma rpow_piece {t φR φd Q β : ℝ} (ht : 0 < t) (hφR : 0 < φR) (hφd : 0 < φd) (hQ : 0 < Q)
    (hβ : 0 < β) (hdQ : φd ≤ Q * φR) :
    t ^ (-1 / β) * (t / φR) ^ (1 + 1 / β) ≤ Q ^ (1 + 1 / β) * t / φd ^ (1 + 1 / β) := by
  have hp : 0 < 1 + 1 / β := by positivity
  have e : t ^ (-1 / β) * (t / φR) ^ (1 + 1 / β) = t / φR ^ (1 + 1 / β) := by
    rw [Real.div_rpow ht.le hφR.le, ← mul_div_assoc, ← Real.rpow_add ht]
    congr 1
    rw [show -1 / β + (1 + 1 / β) = 1 by ring, Real.rpow_one]
  rw [e]
  have h1 : φd ^ (1 + 1 / β) ≤ (Q * φR) ^ (1 + 1 / β) := Real.rpow_le_rpow hφd.le hdQ hp.le
  rw [Real.mul_rpow hQ.le hφR.le] at h1
  have hφRp : 0 < φR ^ (1 + 1 / β) := Real.rpow_pos_of_pos hφR _
  have hφdp : 0 < φd ^ (1 + 1 / β) := Real.rpow_pos_of_pos hφd _
  rw [div_le_div_iff₀ hφRp hφdp]
  nlinarith

end H8

end ErschlerZheng
end

section
open DurrettProbability MarkovChain MarkovHK
open scoped ENNReal
open ErschlerZheng
open H8 in
theorem solution (C₀ cφ β : ℝ) (hC₀ : 0 < C₀) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J ρ : X → X → ℝ)
      (φ : ℝ → ℝ),
      IsTransition J → IsSymmetric J → IsMetric ρ →
      (∀ t : ℝ, 0 < t → ∀ x, heatKernel J t x x ≤ C₀ / t ^ (1 / β)) →
      (∀ r : ℝ, 0 < r → 0 < φ r) → MonotoneOn φ (Set.Ioi 0) →
      (∀ r : ℝ, 0 < r → φ (2 * r) ≤ cφ * φ r) →
      (∀ x, ∀ r : ℝ, 0 < r → ∑' y, (if r < ρ x y then J x y else 0) ≤ 1 / φ r) →
      (∀ x, ∀ r : ℝ, 0 < r → ∑' y, (if ρ x y ≤ r then ρ x y ^ 2 * J x y else 0) ≤ r ^ 2 / φ r) →
      ∀ x y, x ≠ y → ∀ t : ℝ, 0 < t → t ≤ φ (ρ x y) →
        ENNReal.ofReal (heatKernel J t x y) ≤
          ENNReal.ofReal (C * t / φ (ρ x y) ^ (1 + 1 / β)) +
            ENNReal.ofReal t * supNorm (farPart J ρ (β * ρ x y / (3 * (1 + β)))) := by
  obtain ⟨C', hC'0, h4⟩ := Coulhon.nash_of_heatKernel_le C₀ β hC₀ hβ
  obtain ⟨C₂, hC₂0, h5⟩ := CarlenKusuokaStroock.heatKernel_le_exp_davies C' β hC'0 hβ
  set k : ℕ := ⌈3 * (1 + β) / β⌉₊ with hk
  set Q : ℝ := (max 1 cφ) ^ k with hQ
  have hQ1 : 1 ≤ Q := one_le_pow₀ (le_max_left _ _)
  have hQ0 : 0 < Q := by linarith
  refine ⟨C₂ * Real.exp (4 * Q + 144) * Q ^ (1 + 1 / β), by positivity, ?_⟩
  intro X _ _ J ρ φ hJ hJs hρ hdiag hφpos hφmono hφdbl htail hmom x y hxy t ht htφ
  set d := ρ x y with hd_def
  have hd0 : 0 ≤ d := by
    have := hρ.triangle x y x; rw [hρ.self_eq x, hρ.symm y x] at this; linarith
  have hd : 0 < d := lt_of_le_of_ne hd0 (fun h => hxy (hρ.eq_of_eq_zero x y h.symm))
  set R := β * d / (3 * (1 + β)) with hR_def
  have hR : 0 < R := by positivity
  have hφR := hφpos R hR
  have hφd := hφpos d hd
  -- doubling: `φ(d) ≤ Q φ(R)`
  have hdbl : ∀ j : ℕ, φ (2 ^ j * R) ≤ (max 1 cφ) ^ j * φ R := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hpos : 0 < 2 ^ j * R := by positivity
      calc φ (2 ^ (j + 1) * R) = φ (2 * (2 ^ j * R)) := by rw [pow_succ]; ring_nf
        _ ≤ cφ * φ (2 ^ j * R) := hφdbl _ hpos
        _ ≤ max 1 cφ * φ (2 ^ j * R) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hφpos _ hpos).le
        _ ≤ max 1 cφ * ((max 1 cφ) ^ j * φ R) :=
            mul_le_mul_of_nonneg_left ih (le_trans zero_le_one (le_max_left _ _))
        _ = (max 1 cφ) ^ (j + 1) * φ R := by ring
  have hdQ : φ d ≤ Q * φ R := by
    have h1 : d ≤ 2 ^ k * R := by
      have hk1 : 3 * (1 + β) / β ≤ (k : ℝ) := Nat.le_ceil _
      have hk2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self.le
      have e : d = 3 * (1 + β) / β * R := by rw [hR_def]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (hk1.trans hk2) hR.le
    calc φ d ≤ φ (2 ^ k * R) := hφmono hd (by positivity : (0 : ℝ) < 2 ^ k * R) h1
      _ ≤ Q * φ R := hdbl k
  have htR : t / φ R ≤ Q := by
    rw [div_le_iff₀ hφR]; linarith
  -- step 1: the hypothesis of H4
  set U := uniformize (nearPart J ρ R) with hU
  have hUT : IsTransition U := isTransition_uniformize (nearPart_nonneg hJ R)
    (summable_nearPart hJ R) (tsum_nearPart_le hJ R)
  have hpRU : ∀ s u v, heatKernel (nearPart J ρ R) s u v = heatKernel U s u v := by
    intro s u v; rw [heatKernel_eq, heatKernel_eq, uniformize_eq_self hUT]
  have hfar : ∀ u, 1 - ∑' w, nearPart J ρ R u w ≤ 1 / φ R := by
    intro u
    have hfs : Summable (farPart J ρ R u) :=
      Summable.of_nonneg_of_le (farPart_nonneg hJ R u)
        (fun w => by unfold farPart; split_ifs
                     · exact le_rfl
                     · exact hJ.1 u w) (hJ.2.1 u)
    have hsplit : ∑' w, J u w = ∑' w, nearPart J ρ R u w + ∑' w, farPart J ρ R u w := by
      rw [← (summable_nearPart hJ R u).tsum_add hfs]
      exact tsum_congr fun w => (near_add_far J ρ R u w).symm
    have ht := htail u R hR
    have e : ∑' w, farPart J ρ R u w = ∑' w, (if R < ρ u w then J u w else 0) := rfl
    linarith [hJ.2.2 u]
  have hAB : ∀ u v, U u v ≤ J u v + if u = v then 1 / φ R else 0 := by
    intro u v
    have h1 := nearPart_le (ρ := ρ) hJ R u v
    simp only [hU, uniformize]
    split_ifs with h
    · linarith [hfar u]
    · linarith
  have hstep1 : ∀ s : ℝ, 0 < s → ∀ u v,
      heatKernel (nearPart J ρ R) s u v ≤ C₀ * Real.exp (4 * s / φ R) * s ^ (-1 / β) := by
    intro s hs u v
    rw [hpRU]
    have hcmp := heat_le_exp_mul_heat hUT hJ (by positivity : (0 : ℝ) ≤ 1 / φ R) hAB hs.le u v
    have hoff := heat_le_avg_diag hJ hJs hs.le u v
    have hdu := hdiag s hs u
    have hdv := hdiag s hs v
    have hpow : s ^ (-1 / β) = C₀⁻¹ * (C₀ / s ^ (1 / β)) := by
      rw [neg_div, Real.rpow_neg hs.le]; field_simp
    have hexp : Real.exp (1 / φ R * s) ≤ Real.exp (4 * s / φ R) := by
      apply Real.exp_le_exp.mpr
      have h := div_nonneg hs.le hφR.le
      have e1 : 1 / φ R * s = s / φ R := by ring
      have e2 : 4 * s / φ R = 4 * (s / φ R) := by ring
      rw [e1, e2]; linarith
    calc heatKernel U s u v ≤ Real.exp (1 / φ R * s) * heatKernel J s u v := hcmp
      _ ≤ Real.exp (4 * s / φ R) * (C₀ / s ^ (1 / β)) :=
          mul_le_mul hexp (by linarith) (heat_nonneg hJ hs.le u v) (Real.exp_pos _).le
      _ = C₀ * Real.exp (4 * s / φ R) * s ^ (-1 / β) := by
          rw [hpow]; field_simp
  have hN := h4 X J ρ φ R hJ hJs hρ hφR hstep1
  -- step 2: the Davies bound, for every `lam ≥ 0`
  have hmomR : ∀ z, ∑' w, (if ρ z w ≤ R then ρ z w ^ 2 * J z w else 0) ≤ R ^ 2 / φ R :=
    fun z => hmom z R hR
  have hgen : ∀ lam : ℝ, 0 ≤ lam → heatKernel (nearPart J ρ R) t x y ≤ C₂ * t ^ (-1 / β) *
      Real.exp (4 * t / φ R + 72 * (lam ^ 2 * Real.exp (2 * lam * R) * (R ^ 2 / φ R)) * t -
        lam * d) := by
    intro lam hlam
    have hD := davies_bound hJ hρ hR.le hmomR hlam d y
    set ψ : X → ℝ := fun z => lam * max (d - ρ z y) 0 with hψ
    have hDne : daviesSq (nearPart J ρ R) ψ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
    have hDr : (daviesSq (nearPart J ρ R) ψ).toReal ≤
        lam ^ 2 * Real.exp (2 * lam * R) * (R ^ 2 / φ R) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hD
    have h := h5 X J ρ φ R hJ hJs hρ hφR hN ψ hDne t ht x y
    have hψx : ψ x = 0 := by simp [hψ, hd_def]
    have hψy : ψ y = lam * d := by simp [hψ, hρ.self_eq, max_eq_left hd0]
    rw [hψx, hψy] at h
    refine h.trans ?_
    have hC2t : 0 ≤ C₂ * t ^ (-1 / β) := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC2t
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDr (by norm_num : (0:ℝ) ≤ 72))
      ht.le
    linarith
  -- step 3: choose `lam`
  set a := t / φ R with ha
  have ha0 : 0 < a := div_pos ht hφR
  have hexpo : ∃ lam : ℝ, 0 ≤ lam ∧ 4 * t / φ R + 72 * (lam ^ 2 * Real.exp (2 * lam * R) *
      (R ^ 2 / φ R)) * t - lam * d ≤ 4 * Q + 144 + Real.log a * (1 + 1 / β) := by
    have h4t : 4 * t / φ R ≤ 4 * Q := by
      have : 4 * t / φ R = 4 * a := by rw [ha]; ring
      rw [this]; linarith
    rcases lt_or_ge t (φ R) with hlt | hge
    · -- the printed choice `lam = log(φ(R)/t)/(3R)`
      have hlog : 0 < Real.log (φ R / t) := Real.log_pos (by rw [lt_div_iff₀ ht]; linarith)
      refine ⟨Real.log (φ R / t) / (3 * R), by positivity, ?_⟩
      set w := Real.log (φ R / t) / 3 with hw
      have hw0 : 0 ≤ w := by positivity
      have hlamR : Real.log (φ R / t) / (3 * R) * R = w := by rw [hw]; field_simp
      have hloga : Real.log a = -(3 * w) := by
        rw [ha, hw, show (3 : ℝ) * (Real.log (φ R / t) / 3) = Real.log (φ R / t) by ring,
          Real.log_div ht.ne' hφR.ne', Real.log_div hφR.ne' ht.ne']; ring
      have he3 : Real.exp (3 * w) * a = 1 := by
        rw [show 3 * w = Real.log (φ R / t) by rw [hw]; ring, Real.exp_log (by positivity), ha]
        field_simp
      have hsq : w ^ 2 ≤ 2 * Real.exp w := by
        have := Real.quadratic_le_exp_of_nonneg hw0; nlinarith
      have hterm : 72 * ((Real.log (φ R / t) / (3 * R)) ^ 2 *
          Real.exp (2 * (Real.log (φ R / t) / (3 * R)) * R) * (R ^ 2 / φ R)) * t ≤ 144 := by
        have e1 : (Real.log (φ R / t) / (3 * R)) ^ 2 *
            Real.exp (2 * (Real.log (φ R / t) / (3 * R)) * R) * (R ^ 2 / φ R) * t =
            w ^ 2 * Real.exp (2 * w) * a := by
          rw [show 2 * (Real.log (φ R / t) / (3 * R)) * R = 2 * w by rw [← hlamR]; ring, ha]
          rw [← hlamR]; field_simp
        have e2 : Real.exp (2 * w) * Real.exp w = Real.exp (3 * w) := by
          rw [← Real.exp_add]; ring_nf
        have : w ^ 2 * Real.exp (2 * w) * a ≤ 2 := by
          calc w ^ 2 * Real.exp (2 * w) * a ≤ 2 * Real.exp w * Real.exp (2 * w) * a := by
                gcongr
            _ = 2 * (Real.exp (3 * w) * a) := by rw [← e2]; ring
            _ = 2 := by rw [he3]; ring
        calc 72 * ((Real.log (φ R / t) / (3 * R)) ^ 2 *
              Real.exp (2 * (Real.log (φ R / t) / (3 * R)) * R) * (R ^ 2 / φ R)) * t
            = 72 * ((Real.log (φ R / t) / (3 * R)) ^ 2 *
              Real.exp (2 * (Real.log (φ R / t) / (3 * R)) * R) * (R ^ 2 / φ R) * t) := by ring
          _ = 72 * (w ^ 2 * Real.exp (2 * w) * a) := by rw [e1]
          _ ≤ 72 * 2 := by linarith
          _ = 144 := by norm_num
      have hlamd : Real.log (φ R / t) / (3 * R) * d = 3 * w * (1 + 1 / β) := by
        have e : d = 3 * (1 + β) / β * R := by rw [hR_def]; field_simp
        rw [e, hw]; field_simp; ring
      rw [hlamd, hloga]
      nlinarith [hterm, h4t]
    · -- `t ≥ φ(R)`: `lam = 0`
      refine ⟨0, le_rfl, ?_⟩
      have hla : 0 ≤ Real.log a := Real.log_nonneg (by rw [ha, le_div_iff₀ hφR]; linarith)
      have : 0 ≤ Real.log a * (1 + 1 / β) := mul_nonneg hla (by positivity)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
        add_zero, sub_zero]
      linarith
  obtain ⟨lam, hlam, hlamE⟩ := hexpo
  have hpR : heatKernel (nearPart J ρ R) t x y ≤
      C₂ * Real.exp (4 * Q + 144) * Q ^ (1 + 1 / β) * t / φ d ^ (1 + 1 / β) := by
    refine (hgen lam hlam).trans ?_
    have hexp : Real.exp (4 * t / φ R + 72 * (lam ^ 2 * Real.exp (2 * lam * R) * (R ^ 2 / φ R)) *
        t - lam * d) ≤ Real.exp (4 * Q + 144) * a ^ (1 + 1 / β) := by
      rw [Real.rpow_def_of_pos ha0, ← Real.exp_add]
      exact Real.exp_le_exp.mpr hlamE
    have hpiece := rpow_piece ht hφR hφd hQ0 hβ hdQ
    calc C₂ * t ^ (-1 / β) * Real.exp (4 * t / φ R + 72 * (lam ^ 2 * Real.exp (2 * lam * R) *
          (R ^ 2 / φ R)) * t - lam * d)
        ≤ C₂ * t ^ (-1 / β) * (Real.exp (4 * Q + 144) * a ^ (1 + 1 / β)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C₂ * Real.exp (4 * Q + 144) * (t ^ (-1 / β) * (t / φ R) ^ (1 + 1 / β)) := by
          rw [ha]; ring
      _ ≤ C₂ * Real.exp (4 * Q + 144) * (Q ^ (1 + 1 / β) * t / φ d ^ (1 + 1 / β)) :=
          mul_le_mul_of_nonneg_left hpiece (by positivity)
      _ = C₂ * Real.exp (4 * Q + 144) * Q ^ (1 + 1 / β) * t / φ d ^ (1 + 1 / β) := by ring
  -- step 4: Meyer's construction (H6)
  have h6 := BarlowGrigoryanKumagai.heatKernel_le_heatKernel_nearPart_add J ρ hJ hJs hρ R t ht x y
  exact h6.trans (add_le_add (ENNReal.ofReal_le_ofReal hpR) le_rfl)
end
