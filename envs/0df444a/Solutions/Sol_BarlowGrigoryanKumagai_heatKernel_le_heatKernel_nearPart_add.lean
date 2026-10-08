-- Prove2me | solution 1 for BarlowGrigoryanKumagai.heatKernel_le_heatKernel_nearPart_add
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:37:13.940614+00:00
-- url     : https://prove2.me/submissions/4855c15e-21a2-474d-a3be-7fe119758c1d

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

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

lemma le_uniformize_add_far {J ρ : X → X → ℝ} (hJ : IsTransition J) (R : ℝ) (z y : X) :
    J z y ≤ uniformize (nearPart J ρ R) z y + farPart J ρ R z y := by
  rw [← near_add_far J ρ R z y]
  unfold uniformize
  have : 0 ≤ (if z = y then 1 - ∑' w, nearPart J ρ R z w else 0) := by
    split_ifs
    · linarith [tsum_nearPart_le (ρ := ρ) hJ R z]
    · exact le_rfl
  linarith

end MarkovHK
end

section
/-!
# H6: Meyer's construction (Barlow–Grigor'yan–Kumagai, Lemma 3.1(c))

`p(t, x, y) ≤ p_R(t, x, y) + t ‖J^R_2‖_∞`. With `U = uniformize J^R_1` (symmetric, stochastic) and
`M = sup J^R_2`, `J ≤ U + J^R_2` entrywise, so peeling one step on the right,
`Jⁿ⁺¹(x, y) ≤ ∑_z Jⁿ(x, z) U(z, y) + M ≤ Uⁿ⁺¹(x, y) + n M ∑_z U(z, y) + M`, and the column sums of
`U` are one: `Jⁿ ≤ Uⁿ + n M`. Average against the Poisson weights, whose mean is `t`.
-/

open DurrettProbability MarkovChain MarkovHK
open scoped ENNReal

namespace BarlowGrigoryanKumagai

namespace H6

variable {X : Type*} [DecidableEq X]

/-- The key entrywise bound `Jⁿ(x, y) ≤ Uⁿ(x, y) + n M`. -/
lemma stepProb_le {J ρ : X → X → ℝ} (hJ : IsTransition J) (hJs : IsSymmetric J)
    (hρ : IsMetric ρ) (R M : ℝ) (hM : ∀ u v, farPart J ρ R u v ≤ M) :
    ∀ n : ℕ, ∀ x y, stepProb J n x y ≤ stepProb (uniformize (nearPart J ρ R)) n x y + n * M := by
  set U := uniformize (nearPart J ρ R) with hU
  have hUT : IsTransition U := isTransition_uniformize (nearPart_nonneg hJ R)
    (summable_nearPart hJ R) (tsum_nearPart_le hJ R)
  have hUs : IsSymmetric U := uniformize_symm (nearPart_symm hJs hρ R)
  have hUS := isSub_of_isTransition hUT
  have hJS := isSub_of_isTransition hJ
  intro n
  induction n with
  | zero => intro x y; simp [stepProb_zero]
  | succ n ih =>
    intro x y
    have hcolU : Summable (fun z => U z y) := (hUT.2.1 y).congr fun z => hUs y z
    have hcolU1 : ∑' z, U z y = 1 := by
      rw [← hUT.2.2 y]; exact tsum_congr fun z => hUs z y
    have hrowJn := (isSub_stepProb hJS n).2.1 x
    have hrowUn := (isSub_stepProb hUS n).2.1 x
    have hs1 : Summable (fun z => stepProb J n x z * U z y) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (stepProb_nonneg hJS n x z) (hUT.1 z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (hUS.le_one z y) (stepProb_nonneg hJS n x z)
          simpa using this) hrowJn
    have hs2 : Summable (fun z => stepProb J n x z * farPart J ρ R z y) :=
      Summable.of_nonneg_of_le
        (fun z => mul_nonneg (stepProb_nonneg hJS n x z) (farPart_nonneg hJ R z y))
        (fun z => mul_le_mul_of_nonneg_left (hM z y) (stepProb_nonneg hJS n x z))
        (hrowJn.mul_right M)
    have hs3 : Summable (fun z => stepProb U n x z * U z y) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (stepProb_nonneg hUS n x z) (hUT.1 z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (hUS.le_one z y) (stepProb_nonneg hUS n x z)
          simpa using this) hrowUn
    rw [stepProb_succ' hJS, stepProb_succ' hUS]
    calc ∑' z, stepProb J n x z * J z y
        ≤ ∑' z, (stepProb J n x z * U z y + stepProb J n x z * farPart J ρ R z y) := by
          refine Summable.tsum_le_tsum (fun z => ?_) ?_ (hs1.add hs2)
          · rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (le_uniformize_add_far hJ R z y)
              (stepProb_nonneg hJS n x z)
          · exact Summable.of_nonneg_of_le
              (fun z => mul_nonneg (stepProb_nonneg hJS n x z) (hJ.1 z y))
              (fun z => by
                have := mul_le_mul_of_nonneg_left (hJS.le_one z y) (stepProb_nonneg hJS n x z)
                simpa using this) hrowJn
      _ = ∑' z, stepProb J n x z * U z y + ∑' z, stepProb J n x z * farPart J ρ R z y :=
          hs1.tsum_add hs2
      _ ≤ ∑' z, (stepProb U n x z * U z y + (n * M) * U z y) + ∑' z, stepProb J n x z * M := by
          refine add_le_add ?_ ?_
          · refine Summable.tsum_le_tsum (fun z => ?_) hs1 (hs3.add (hcolU.mul_left _))
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right (ih x z) (hUT.1 z y)
          · exact Summable.tsum_le_tsum
              (fun z => mul_le_mul_of_nonneg_left (hM z y) (stepProb_nonneg hJS n x z)) hs2
              (hrowJn.mul_right M)
      _ = ∑' z, stepProb U n x z * U z y + (n + 1 : ℕ) * M := by
          rw [hs3.tsum_add (hcolU.mul_left _), tsum_mul_left, hcolU1, tsum_mul_right,
            tsum_stepProb hJ n x]
          push_cast; ring

end H6

end BarlowGrigoryanKumagai
end

section
open DurrettProbability MarkovChain MarkovHK
open scoped ENNReal
open BarlowGrigoryanKumagai
open H6 in
theorem solution {X : Type*} [Countable X] [DecidableEq X]
    (J ρ : X → X → ℝ) (hJ : IsTransition J) (hJs : IsSymmetric J) (hρ : IsMetric ρ) (R t : ℝ)
    (ht : 0 < t) (x y : X) :
    ENNReal.ofReal (heatKernel J t x y) ≤
      ENNReal.ofReal (heatKernel (nearPart J ρ R) t x y) +
        ENNReal.ofReal t * supNorm (farPart J ρ R) := by
  set U := uniformize (nearPart J ρ R) with hU
  have hUT : IsTransition U := isTransition_uniformize (nearPart_nonneg hJ R)
    (summable_nearPart hJ R) (tsum_nearPart_le hJ R)
  have hUS := isSub_of_isTransition hUT
  have hJS := isSub_of_isTransition hJ
  -- the sup norm of the far part is finite
  have hsup_le : supNorm (farPart J ρ R) ≤ 1 := by
    unfold supNorm
    refine iSup_le fun u => iSup_le fun v => ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : farPart J ρ R u v ≤ J u v := by
      unfold farPart; split_ifs
      · exact le_rfl
      · exact hJ.1 u v
    exact h1.trans (hJS.le_one u v)
  have hsup_ne : supNorm (farPart J ρ R) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hsup_le
  set M := (supNorm (farPart J ρ R)).toReal with hMdef
  have hM : ∀ u v, farPart J ρ R u v ≤ M := by
    intro u v
    rw [hMdef, ← ENNReal.ofReal_le_iff_le_toReal hsup_ne]
    unfold supNorm
    exact le_iSup_of_le u (le_iSup_of_le v le_rfl)
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hkey := stepProb_le hJ hJs hρ R M hM
  -- average against the Poisson weights
  have hreal : heatKernel J t x y ≤ heatKernel (nearPart J ρ R) t x y + t * M := by
    rw [heatKernel_eq, heatKernel_eq, uniformize_eq_self hJ, ← hU]
    have hsJ := summable_heat hJS ht.le x y
    have hsU := summable_heat hUS ht.le x y
    have hsN := (summable_poi_mul t).mul_right M
    calc ∑' n, poi t n * stepProb J n x y
        ≤ ∑' n, (poi t n * stepProb U n x y + poi t n * n * M) := by
          refine Summable.tsum_le_tsum (fun n => ?_) hsJ (hsU.add hsN)
          rw [mul_assoc (poi t n), ← mul_add]
          exact mul_le_mul_of_nonneg_left (hkey n x y) (poi_nonneg ht.le n)
      _ = ∑' n, poi t n * stepProb U n x y + t * M := by
          rw [hsU.tsum_add hsN, tsum_mul_right, (hasSum_poi_mul t).tsum_eq]
  have hpR : 0 ≤ heatKernel (nearPart J ρ R) t x y := by
    rw [heatKernel_eq]
    exact tsum_nonneg fun n => mul_nonneg (poi_nonneg ht.le n) (stepProb_nonneg hUS n x y)
  calc ENNReal.ofReal (heatKernel J t x y)
      ≤ ENNReal.ofReal (heatKernel (nearPart J ρ R) t x y + t * M) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (heatKernel (nearPart J ρ R) t x y) + ENNReal.ofReal (t * M) :=
        ENNReal.ofReal_add hpR (mul_nonneg ht.le hM0)
    _ = ENNReal.ofReal (heatKernel (nearPart J ρ R) t x y) +
          ENNReal.ofReal t * supNorm (farPart J ρ R) := by
        rw [ENNReal.ofReal_mul ht.le, hMdef, ENNReal.ofReal_toReal hsup_ne]
end
