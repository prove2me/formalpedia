-- Prove2me | solution 1 for BirkhoffGlobalSection.critical_estimate_radial_pos
-- status  : ACCEPTED   (disprove)
-- author  : @caleb
-- created : 2026-10-01T00:33:21.602834+00:00
-- url     : https://prove2.me/submissions/25295d74-7991-4ef1-88b5-15f35c6db26b

import Definitions.Def_BirkhoffGlobalSection_EHCriticalConvexity
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace BirkhoffGlobalSection

noncomputable section

/-- The real exponential is the sum of its power series. -/
lemma hasSum_exp_series (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / Nat.cast (Nat.factorial n)) (Real.exp x) := by
  have hsumm : Summable (fun n : ℕ => x ^ n / Nat.cast (Nat.factorial n)) := by
    have h := NormedSpace.expSeries_summable (𝕂 := ℝ) (𝔸 := ℝ) x
    rwa [NormedSpace.expSeries_apply_eq_div'] at h
  have hexp : Real.exp x = ∑' n : ℕ, x ^ n / Nat.cast (Nat.factorial n) := by
    conv_lhs => rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div x
  rw [hexp]
  exact hsumm.hasSum

/-- One step of the geometric majorant for the exponential tail. -/
lemma exp_tail_step {x : ℝ} (hx : 0 ≤ x) {N M : ℕ} (hNM : N ≤ M) :
    x ^ (M + 1) / Nat.cast (Nat.factorial (M + 1))
      ≤ (x ^ M / Nat.cast (Nat.factorial M)) * (x / ((N : ℝ) + 1)) := by
  have hM : (0 : ℝ) < Nat.cast (Nat.factorial M) :=
    Nat.cast_pos.mpr (Nat.factorial_pos M)
  have hle : x / ((M : ℝ) + 1) ≤ x / ((N : ℝ) + 1) :=
    div_le_div_of_nonneg_left hx (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hNM 1)
  calc x ^ (M + 1) / Nat.cast (Nat.factorial (M + 1))
      = (x ^ M / Nat.cast (Nat.factorial M)) * (x / ((M : ℝ) + 1)) := by
        rw [pow_succ, Nat.factorial_succ]
        push_cast
        field_simp
    _ ≤ (x ^ M / Nat.cast (Nat.factorial M)) * (x / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-- Geometric majorant for the exponential series tail. -/
lemma exp_tail_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (k : ℕ) :
    x ^ (k + N) / Nat.cast (Nat.factorial (k + N))
      ≤ (x ^ N / Nat.cast (Nat.factorial N)) * (x / ((N : ℝ) + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : k + 1 + N = (k + N) + 1 := by omega
    rw [e1]
    calc x ^ ((k + N) + 1) / Nat.cast (Nat.factorial ((k + N) + 1))
        ≤ (x ^ (k + N) / Nat.cast (Nat.factorial (k + N)))
            * (x / ((N : ℝ) + 1)) :=
          exp_tail_step hx (Nat.le_add_left N k)
      _ ≤ ((x ^ N / Nat.cast (Nat.factorial N)) * (x / ((N : ℝ) + 1)) ^ k)
            * (x / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ = (x ^ N / Nat.cast (Nat.factorial N)) * (x / ((N : ℝ) + 1)) ^ (k + 1) := by
          ring

/-- Upper bound for `Real.exp` via partial sum plus geometric tail. -/
lemma exp_upper {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hq : x / ((N : ℝ) + 1) < 1) :
    Real.exp x ≤ (∑ i ∈ Finset.range N, x ^ i / Nat.cast (Nat.factorial i))
      + (x ^ N / Nat.cast (Nat.factorial N)) * (1 - x / ((N : ℝ) + 1))⁻¹ := by
  have hsumm : Summable (fun n : ℕ => x ^ n / Nat.cast (Nat.factorial n)) :=
    (hasSum_exp_series x).summable
  have hexp : Real.exp x = ∑' n : ℕ, x ^ n / Nat.cast (Nat.factorial n) :=
    (hasSum_exp_series x).tsum_eq.symm
  have hq0 : (0 : ℝ) ≤ x / ((N : ℝ) + 1) := by positivity
  have hptw : ∀ k : ℕ, x ^ (k + N) / Nat.cast (Nat.factorial (k + N))
      ≤ (x ^ N / Nat.cast (Nat.factorial N)) * (x / ((N : ℝ) + 1)) ^ k :=
    fun k => exp_tail_le hx N k
  have hgeo : Summable
      (fun k : ℕ => (x ^ N / Nat.cast (Nat.factorial N))
        * (x / ((N : ℝ) + 1)) ^ k) :=
    (summable_geometric_of_lt_one hq0 hq).mul_left _
  have htail : Summable
      (fun k : ℕ => x ^ (k + N) / Nat.cast (Nat.factorial (k + N))) :=
    hgeo.of_nonneg_of_le (fun k => by positivity) hptw
  have hle : (∑' k : ℕ, x ^ (k + N) / Nat.cast (Nat.factorial (k + N)))
      ≤ ∑' k : ℕ, (x ^ N / Nat.cast (Nat.factorial N))
        * (x / ((N : ℝ) + 1)) ^ k :=
    htail.tsum_le_tsum hptw hgeo
  have hgeo_val :
      (∑' k : ℕ, (x ^ N / Nat.cast (Nat.factorial N))
        * (x / ((N : ℝ) + 1)) ^ k)
      = (x ^ N / Nat.cast (Nat.factorial N)) * (1 - x / ((N : ℝ) + 1))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
  have hsplit : (∑ i ∈ Finset.range N, x ^ i / Nat.cast (Nat.factorial i))
      + (∑' i : ℕ, x ^ (i + N) / Nat.cast (Nat.factorial (i + N)))
      = ∑' n : ℕ, x ^ n / Nat.cast (Nat.factorial n) :=
    Summable.sum_add_tsum_nat_add N hsumm
  have htail_eq : (∑' i : ℕ, x ^ (i + N) / Nat.cast (Nat.factorial (i + N)))
      = ∑' k : ℕ, x ^ (k + N) / Nat.cast (Nat.factorial (k + N)) := by
    apply tsum_congr; intro k; rw [add_comm k N]
  have hmain : (∑' i : ℕ, x ^ (i + N) / Nat.cast (Nat.factorial (i + N)))
      ≤ (x ^ N / Nat.cast (Nat.factorial N)) * (1 - x / ((N : ℝ) + 1))⁻¹ := by
    rw [htail_eq]
    exact hle.trans (le_of_eq hgeo_val)
  have hexp2 : Real.exp x
      = (∑ i ∈ Finset.range N, x ^ i / Nat.cast (Nat.factorial i))
      + (∑' i : ℕ, x ^ (i + N) / Nat.cast (Nat.factorial (i + N))) :=
    hexp.trans hsplit.symm
  rw [hexp2]
  linarith [hmain]

/-- Lower bound for `exp 1.9` from the degree-10 partial sum. -/
lemma exp19_lb : (6.685 : ℝ) ≤ Real.exp 1.9 := by
  have hsumm : Summable
      (fun n : ℕ => (1.9 : ℝ) ^ n / Nat.cast (Nat.factorial n)) :=
    (hasSum_exp_series 1.9).summable
  have hle := Summable.sum_le_tsum (Finset.range 10)
    (fun k _ => by positivity) hsumm
  rw [(hasSum_exp_series 1.9).tsum_eq] at hle
  have hval : (6.685 : ℝ)
      ≤ ∑ i ∈ Finset.range 10, (1.9 : ℝ) ^ i / Nat.cast (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ]
  exact le_trans hval hle

/-- Upper bound for `exp 1.9` from partial sum plus geometric tail. -/
lemma exp19_ub : Real.exp 1.9 ≤ (6.686 : ℝ) := by
  have h := exp_upper (x := 1.9) (N := 10) (by norm_num) (by norm_num)
  have hval :
      (∑ i ∈ Finset.range 10, (1.9 : ℝ) ^ i / Nat.cast (Nat.factorial i))
        + ((1.9 : ℝ) ^ 10 / Nat.cast (Nat.factorial 10))
          * (1 - 1.9 / (Nat.cast (10 : ℕ) + 1))⁻¹ ≤ (6.686 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact le_trans h hval

/-- Lower bound for `exp 3.8` from the degree-13 partial sum. -/
lemma exp38_lb : (44.69 : ℝ) ≤ Real.exp 3.8 := by
  have hsumm : Summable
      (fun n : ℕ => (3.8 : ℝ) ^ n / Nat.cast (Nat.factorial n)) :=
    (hasSum_exp_series 3.8).summable
  have hle := Summable.sum_le_tsum (Finset.range 13)
    (fun k _ => by positivity) hsumm
  rw [(hasSum_exp_series 3.8).tsum_eq] at hle
  have hval : (44.69 : ℝ)
      ≤ ∑ i ∈ Finset.range 13, (3.8 : ℝ) ^ i / Nat.cast (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ]
  exact le_trans hval hle

/-- Upper bound for `exp 3.8` from partial sum plus geometric tail. -/
lemma exp38_ub : Real.exp 3.8 ≤ (44.71 : ℝ) := by
  have h := exp_upper (x := 3.8) (N := 13) (by norm_num) (by norm_num)
  have hval :
      (∑ i ∈ Finset.range 13, (3.8 : ℝ) ^ i / Nat.cast (Nat.factorial i))
        + ((3.8 : ℝ) ^ 13 / Nat.cast (Nat.factorial 13))
          * (1 - 3.8 / (Nat.cast (13 : ℕ) + 1))⁻¹ ≤ (44.71 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact le_trans h hval

/-- Bounds for `exp (-1.9)` via reciprocal. -/
lemma exp_neg19_lb : (1 / 6.686 : ℝ) ≤ Real.exp (-1.9) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos 1.9) exp19_ub

lemma exp_neg19_ub : Real.exp (-1.9) ≤ (1 / 6.685 : ℝ) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) exp19_lb

/-- Bounds for `exp (-3.8)` via reciprocal. -/
lemma exp_neg38_lb : (1 / 44.71 : ℝ) ≤ Real.exp (-3.8) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos 3.8) exp38_ub

lemma exp_neg38_ub : Real.exp (-3.8) ≤ (1 / 44.69 : ℝ) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) exp38_lb

/-- Enclosures for the hyperbolic values at `1.9` and `3.8`. -/
lemma cosh19_bounds :
    (3.4172 : ℝ) ≤ Real.cosh 1.9 ∧ Real.cosh 1.9 ≤ 3.4178 := by
  rw [Real.cosh_eq]
  constructor <;> linarith [exp19_lb, exp19_ub, exp_neg19_lb, exp_neg19_ub]

lemma sinh19_bounds :
    (3.2677 : ℝ) ≤ Real.sinh 1.9 ∧ Real.sinh 1.9 ≤ 3.2683 := by
  rw [Real.sinh_eq]
  constructor <;> linarith [exp19_lb, exp19_ub, exp_neg19_lb, exp_neg19_ub]

lemma cosh38_bounds :
    (22.356 : ℝ) ≤ Real.cosh 3.8 ∧ Real.cosh 3.8 ≤ 22.367 := by
  rw [Real.cosh_eq]
  constructor <;> linarith [exp38_lb, exp38_ub, exp_neg38_lb, exp_neg38_ub]

lemma sinh38_bounds :
    (22.333 : ℝ) ≤ Real.sinh 3.8 ∧ Real.sinh 3.8 ≤ 22.344 := by
  rw [Real.sinh_eq]
  constructor <;> linarith [exp38_lb, exp38_ub, exp_neg38_lb, exp_neg38_ub]

/-- Derivative of `fun y => 2 * y`. -/
lemma hasDerivAt_two_mul (x : ℝ) : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
  simpa using (hasDerivAt_id x).const_mul 2

/-- First derivative of `ehF1`. -/
lemma hasDerivAt_ehF1 (x : ℝ) :
    HasDerivAt ehF1 (Real.cos (2 * x) / 4) x := by
  have hs := HasDerivAt.comp x (Real.hasDerivAt_sin (2 * x)) (hasDerivAt_two_mul x)
  have hd := hs.div_const 8
  have hfun : (fun y : ℝ => (Real.sin ∘ (fun z => 2 * z)) y / 8) = ehF1 := by
    funext y; simp [ehF1, Function.comp_apply]
  rw [hfun] at hd
  have hderiv : Real.cos (2 * x) * 2 / 8 = Real.cos (2 * x) / 4 := by ring
  rw [hderiv] at hd
  exact hd

/-- First derivative of `ehF2`. -/
lemma hasDerivAt_ehF2 (x : ℝ) :
    HasDerivAt ehF2 (Real.cosh (2 * x) / 4) x := by
  have hs := HasDerivAt.comp x (Real.hasDerivAt_sinh (2 * x)) (hasDerivAt_two_mul x)
  have hd := hs.div_const 8
  have hfun : (fun y : ℝ => (Real.sinh ∘ (fun z => 2 * z)) y / 8) = ehF2 := by
    funext y; simp [ehF2, Function.comp_apply]
  rw [hfun] at hd
  have hderiv : Real.cosh (2 * x) * 2 / 8 = Real.cosh (2 * x) / 4 := by ring
  rw [hderiv] at hd
  exact hd

/-- First derivative of `ehW1`. -/
lemma hasDerivAt_ehW1 (x : ℝ) :
    HasDerivAt ehW1
      (Real.sinh x * Real.cosh x - Real.sinh x / 2
        - Real.sinh (2 * x) * Real.cosh (2 * x) / 32) x := by
  have hA := (HasDerivAt.mul (Real.hasDerivAt_cosh x)
    (Real.hasDerivAt_cosh x)).div_const 2
  have hB : HasDerivAt (fun y : ℝ => Real.cosh y / 2) (Real.sinh x / 2) x :=
    (Real.hasDerivAt_cosh x).div_const 2
  have c1 : HasDerivAt (Real.sinh ∘ (fun y : ℝ => 2 * y))
      (Real.cosh (2 * x) * 2) x :=
    HasDerivAt.comp x (Real.hasDerivAt_sinh (2 * x)) (hasDerivAt_two_mul x)
  have hC := (HasDerivAt.mul c1 c1).div_const 128
  have hd := HasDerivAt.sub (HasDerivAt.sub hA hB) hC
  have hfun : ((((fun y : ℝ => (Real.cosh * Real.cosh) y / 2)
      - (fun y : ℝ => Real.cosh y / 2))
      - (fun y : ℝ => ((Real.sinh ∘ (fun z => 2 * z))
        * (Real.sinh ∘ (fun z => 2 * z))) y / 128))) = ehW1 := by
    funext y
    simp only [ehW1, Pi.sub_apply, Pi.mul_apply, Function.comp_apply, pow_two]
  rw [hfun] at hd
  simp only [Function.comp_apply] at hd
  have hderiv :
      ((Real.sinh x * Real.cosh x + Real.cosh x * Real.sinh x) / 2
        - Real.sinh x / 2)
        - ((Real.cosh (2 * x) * 2) * Real.sinh (2 * x)
          + Real.sinh (2 * x) * (Real.cosh (2 * x) * 2)) / 128
      = Real.sinh x * Real.cosh x - Real.sinh x / 2
        - Real.sinh (2 * x) * Real.cosh (2 * x) / 32 := by
    ring
  rw [hderiv] at hd
  exact hd

/-- First derivative of `ehW2`. -/
lemma hasDerivAt_ehW2 (x : ℝ) :
    HasDerivAt ehW2
      (Real.sin x * Real.cos x
        - Real.sin (2 * x) * Real.cos (2 * x) / 32) x := by
  have hA := (HasDerivAt.mul (Real.hasDerivAt_cos x)
    (Real.hasDerivAt_cos x)).div_const 2
  have s1 : HasDerivAt (Real.sin ∘ (fun y : ℝ => 2 * y))
      (Real.cos (2 * x) * 2) x :=
    HasDerivAt.comp x (Real.hasDerivAt_sin (2 * x)) (hasDerivAt_two_mul x)
  have hC := (HasDerivAt.mul s1 s1).div_const 128
  have hd := HasDerivAt.sub hA.neg hC
  have hfun : ((-(fun y : ℝ => (Real.cos * Real.cos) y / 2))
      - (fun y : ℝ => ((Real.sin ∘ (fun z => 2 * z))
        * (Real.sin ∘ (fun z => 2 * z))) y / 128)) = ehW2 := by
    funext y
    simp only [ehW2, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
      Function.comp_apply, pow_two]
    ring
  rw [hfun] at hd
  simp only [Function.comp_apply] at hd
  have hderiv :
      -(((-Real.sin x) * Real.cos x + Real.cos x * (-Real.sin x)) / 2)
        - ((Real.cos (2 * x) * 2) * Real.sin (2 * x)
          + Real.sin (2 * x) * (Real.cos (2 * x) * 2)) / 128
      = Real.sin x * Real.cos x
        - Real.sin (2 * x) * Real.cos (2 * x) / 32 := by
    ring
  rw [hderiv] at hd
  exact hd

/-- Second derivative of the `cos (2·) / 4` factor. -/
lemma hasDerivAt_F1d (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (2 * y) / 4)
      (-Real.sin (2 * x) / 2) x := by
  have hs := HasDerivAt.comp x (Real.hasDerivAt_cos (2 * x)) (hasDerivAt_two_mul x)
  have hd := hs.div_const 4
  have hfun : (fun y : ℝ => (Real.cos ∘ (fun z => 2 * z)) y / 4)
      = (fun y : ℝ => Real.cos (2 * y) / 4) := by
    funext y; simp [Function.comp_apply]
  rw [hfun] at hd
  have hderiv : -Real.sin (2 * x) * 2 / 4 = -Real.sin (2 * x) / 2 := by ring
  rw [hderiv] at hd
  exact hd

/-- Second derivative of the `cosh (2·) / 4` factor. -/
lemma hasDerivAt_F2d (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cosh (2 * y) / 4)
      (Real.sinh (2 * x) / 2) x := by
  have hs := HasDerivAt.comp x (Real.hasDerivAt_cosh (2 * x)) (hasDerivAt_two_mul x)
  have hd := hs.div_const 4
  have hfun : (fun y : ℝ => (Real.cosh ∘ (fun z => 2 * z)) y / 4)
      = (fun y : ℝ => Real.cosh (2 * y) / 4) := by
    funext y; simp [Function.comp_apply]
  rw [hfun] at hd
  have hderiv : Real.sinh (2 * x) * 2 / 4 = Real.sinh (2 * x) / 2 := by ring
  rw [hderiv] at hd
  exact hd

/-- Second derivative of the `ehW1` first-derivative form. -/
lemma hasDerivAt_W1d (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sinh y * Real.cosh y - Real.sinh y / 2
        - Real.sinh (2 * y) * Real.cosh (2 * y) / 32)
      ((Real.cosh x ^ 2 + Real.sinh x ^ 2) - Real.cosh x / 2
        - (Real.cosh (2 * x) ^ 2 + Real.sinh (2 * x) ^ 2) * 2 / 32) x := by
  have m1 := HasDerivAt.mul (Real.hasDerivAt_sinh x) (Real.hasDerivAt_cosh x)
  have t2 : HasDerivAt (fun y : ℝ => Real.sinh y / 2) (Real.cosh x / 2) x :=
    (Real.hasDerivAt_sinh x).div_const 2
  have c1 : HasDerivAt (Real.sinh ∘ (fun y : ℝ => 2 * y))
      (Real.cosh (2 * x) * 2) x :=
    HasDerivAt.comp x (Real.hasDerivAt_sinh (2 * x)) (hasDerivAt_two_mul x)
  have c2 : HasDerivAt (Real.cosh ∘ (fun y : ℝ => 2 * y))
      (Real.sinh (2 * x) * 2) x :=
    HasDerivAt.comp x (Real.hasDerivAt_cosh (2 * x)) (hasDerivAt_two_mul x)
  have m2 := HasDerivAt.mul c1 c2
  have t3 : HasDerivAt (fun y : ℝ => ((Real.sinh ∘ (fun z => 2 * z))
      * (Real.cosh ∘ (fun z => 2 * z))) y / 32) _ x :=
    m2.div_const 32
  have hd := HasDerivAt.sub (HasDerivAt.sub m1 t2) t3
  have hfun : (((Real.sinh * Real.cosh - (fun y : ℝ => Real.sinh y / 2))
      - (fun y : ℝ => ((Real.sinh ∘ (fun z => 2 * z))
        * (Real.cosh ∘ (fun z => 2 * z))) y / 32)))
      = (fun y : ℝ => Real.sinh y * Real.cosh y - Real.sinh y / 2
        - Real.sinh (2 * y) * Real.cosh (2 * y) / 32) := by
    funext y
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
  rw [hfun] at hd
  simp only [Function.comp_apply] at hd
  have hderiv :
      ((Real.cosh x * Real.cosh x + Real.sinh x * Real.sinh x)
        - Real.cosh x / 2)
        - ((Real.cosh (2 * x) * 2) * Real.cosh (2 * x)
          + Real.sinh (2 * x) * (Real.sinh (2 * x) * 2)) / 32
      = (Real.cosh x ^ 2 + Real.sinh x ^ 2) - Real.cosh x / 2
        - (Real.cosh (2 * x) ^ 2 + Real.sinh (2 * x) ^ 2) * 2 / 32 := by
    ring
  rw [hderiv] at hd
  exact hd

/-- Second derivative of the `ehW2` first-derivative form. -/
lemma hasDerivAt_W2d (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin y * Real.cos y
        - Real.sin (2 * y) * Real.cos (2 * y) / 32)
      ((Real.cos x ^ 2 - Real.sin x ^ 2)
        - (Real.cos (2 * x) ^ 2 - Real.sin (2 * x) ^ 2) * 2 / 32) x := by
  have m1 := HasDerivAt.mul (Real.hasDerivAt_sin x) (Real.hasDerivAt_cos x)
  have s1 : HasDerivAt (Real.sin ∘ (fun y : ℝ => 2 * y))
      (Real.cos (2 * x) * 2) x :=
    HasDerivAt.comp x (Real.hasDerivAt_sin (2 * x)) (hasDerivAt_two_mul x)
  have c1 : HasDerivAt (Real.cos ∘ (fun y : ℝ => 2 * y))
      (-Real.sin (2 * x) * 2) x :=
    HasDerivAt.comp x (Real.hasDerivAt_cos (2 * x)) (hasDerivAt_two_mul x)
  have m2 := HasDerivAt.mul s1 c1
  have t3 : HasDerivAt (fun y : ℝ => ((Real.sin ∘ (fun z => 2 * z))
      * (Real.cos ∘ (fun z => 2 * z))) y / 32) _ x :=
    m2.div_const 32
  have hd := HasDerivAt.sub m1 t3
  have hfun : (((Real.sin * Real.cos)
      - (fun y : ℝ => ((Real.sin ∘ (fun z => 2 * z))
        * (Real.cos ∘ (fun z => 2 * z))) y / 32)))
      = (fun y : ℝ => Real.sin y * Real.cos y
        - Real.sin (2 * y) * Real.cos (2 * y) / 32) := by
    funext y
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
  rw [hfun] at hd
  simp only [Function.comp_apply] at hd
  have hderiv :
      (Real.cos x * Real.cos x + Real.sin x * (-Real.sin x))
        - ((Real.cos (2 * x) * 2) * Real.cos (2 * x)
          + Real.sin (2 * x) * ((-Real.sin (2 * x)) * 2)) / 32
      = (Real.cos x ^ 2 - Real.sin x ^ 2)
        - (Real.cos (2 * x) ^ 2 - Real.sin (2 * x) ^ 2) * 2 / 32 := by
    ring
  rw [hderiv] at hd
  exact hd

/-- Closed forms for the first derivatives as functions. -/
lemma dF1 : deriv ehF1 = fun x => Real.cos (2 * x) / 4 :=
  funext fun x => (hasDerivAt_ehF1 x).deriv

lemma dF2 : deriv ehF2 = fun x => Real.cosh (2 * x) / 4 :=
  funext fun x => (hasDerivAt_ehF2 x).deriv

lemma dW1 : deriv ehW1 = fun x => Real.sinh x * Real.cosh x
    - Real.sinh x / 2 - Real.sinh (2 * x) * Real.cosh (2 * x) / 32 :=
  funext fun x => (hasDerivAt_ehW1 x).deriv

lemma dW2 : deriv ehW2 = fun x => Real.sin x * Real.cos x
    - Real.sin (2 * x) * Real.cos (2 * x) / 32 :=
  funext fun x => (hasDerivAt_ehW2 x).deriv

/-- Second derivatives at the witness coordinates. -/
lemma ddF1_0 : deriv (deriv ehF1) 0 = 0 := by
  rw [dF1]
  exact (hasDerivAt_F1d 0).deriv.trans (by norm_num [Real.sin_zero])

lemma ddF2_19 : deriv (deriv ehF2) 1.9 = Real.sinh (2 * 1.9) / 2 := by
  rw [dF2]
  exact (hasDerivAt_F2d 1.9).deriv

lemma ddW1_eq : deriv (deriv ehW1) 1.9
    = (Real.cosh 1.9 ^ 2 + Real.sinh 1.9 ^ 2) - Real.cosh 1.9 / 2
      - (Real.cosh (2 * 1.9) ^ 2 + Real.sinh (2 * 1.9) ^ 2) * 2 / 32 := by
  rw [dW1]
  exact (hasDerivAt_W1d 1.9).deriv

lemma ddW2_0 : deriv (deriv ehW2) 0 = 15 / 16 := by
  rw [dW2]
  exact (hasDerivAt_W2d 0).deriv.trans
    (by norm_num [Real.sin_zero, Real.cos_zero])

/-- Exact values at `0`. -/
lemma ehF1_0 : ehF1 0 = 0 := by norm_num [ehF1, Real.sin_zero]

lemma ehW2_0 : ehW2 0 = -1 / 2 := by
  norm_num [ehW2, Real.sin_zero, Real.cos_zero]

lemma dW2_0 : deriv ehW2 0 = 0 := by
  rw [dW2]
  norm_num [Real.sin_zero]

/-- The `2 * 1.9 = 3.8` bridge. -/
lemma h3819 : (2 : ℝ) * 1.9 = 3.8 := by norm_num

/-- Enclosures for the first- and second-derivative factors at `1.9`. -/
lemma ehF2_19_lb : (2.791 : ℝ) ≤ ehF2 1.9 := by
  have h : ehF2 1.9 = Real.sinh 3.8 / 8 := by simp [ehF2, h3819]
  rw [h]
  linarith [sinh38_bounds.1]

lemma dF2_19_ub : deriv ehF2 1.9 ≤ (5.59175 : ℝ) := by
  have h : deriv ehF2 1.9 = Real.cosh 3.8 / 4 := by simp [dF2, h3819]
  rw [h]
  linarith [cosh38_bounds.2]

lemma ddF2_19_ub : deriv (deriv ehF2) 1.9 ≤ (11.173 : ℝ) := by
  have h : deriv (deriv ehF2) 1.9 = Real.sinh 3.8 / 2 := by simp [ddF2_19, h3819]
  rw [h]
  linarith [sinh38_bounds.2]

/-- Enclosure for `ehW1 1.9`. -/
lemma ehW1_19_bounds : (0.229 : ℝ) ≤ ehW1 1.9 ∧ ehW1 1.9 ≤ 0.236 := by
  have h : ehW1 1.9 = Real.cosh 1.9 ^ 2 / 2 - Real.cosh 1.9 / 2
      - Real.sinh 3.8 ^ 2 / 128 := by
    simp [ehW1, h3819]
  rw [h]
  obtain ⟨c1l, c1u⟩ := cosh19_bounds
  obtain ⟨s3l, s3u⟩ := sinh38_bounds
  have e1 : Real.cosh 1.9 ^ 2 ≤ 3.4178 ^ 2 :=
    pow_le_pow_left₀ (by linarith) c1u 2
  have e2 : (3.4172 : ℝ) ^ 2 ≤ Real.cosh 1.9 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) c1l 2
  have e3 : (22.333 : ℝ) ^ 2 ≤ Real.sinh 3.8 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) s3l 2
  have e4 : Real.sinh 3.8 ^ 2 ≤ 22.344 ^ 2 :=
    pow_le_pow_left₀ (by linarith) s3u 2
  constructor <;> linarith

/-- Enclosure for `deriv ehW1 1.9`. -/
lemma dW1_19_bounds :
    (-6.09 : ℝ) ≤ deriv ehW1 1.9 ∧ deriv ehW1 1.9 ≤ -6.06 := by
  have h : deriv ehW1 1.9 = Real.sinh 1.9 * Real.cosh 1.9
      - Real.sinh 1.9 / 2 - Real.sinh 3.8 * Real.cosh 3.8 / 32 := by
    simp [dW1, h3819]
  rw [h]
  obtain ⟨c1l, c1u⟩ := cosh19_bounds
  obtain ⟨s1l, s1u⟩ := sinh19_bounds
  obtain ⟨c3l, c3u⟩ := cosh38_bounds
  obtain ⟨s3l, s3u⟩ := sinh38_bounds
  have p1u : Real.sinh 1.9 * Real.cosh 1.9 ≤ 3.2683 * 3.4178 :=
    mul_le_mul s1u c1u (by linarith) (by norm_num)
  have p1l : 3.2677 * 3.4172 ≤ Real.sinh 1.9 * Real.cosh 1.9 :=
    mul_le_mul s1l c1l (by norm_num) (by linarith)
  have p3u : Real.sinh 3.8 * Real.cosh 3.8 ≤ 22.344 * 22.367 :=
    mul_le_mul s3u c3u (by linarith) (by norm_num)
  have p3l : 22.333 * 22.356 ≤ Real.sinh 3.8 * Real.cosh 3.8 :=
    mul_le_mul s3l c3l (by norm_num) (by linarith)
  constructor <;> linarith

/-- Enclosure for `deriv (deriv ehW1) 1.9`. -/
lemma ddW1_19_bounds : (-41.83 : ℝ) ≤ deriv (deriv ehW1) 1.9 ∧
    deriv (deriv ehW1) 1.9 ≤ -41.75 := by
  have h : deriv (deriv ehW1) 1.9
      = (Real.cosh 1.9 ^ 2 + Real.sinh 1.9 ^ 2) - Real.cosh 1.9 / 2
        - (Real.cosh 3.8 ^ 2 + Real.sinh 3.8 ^ 2) * 2 / 32 := by
    simp [ddW1_eq, h3819]
  rw [h]
  obtain ⟨c1l, c1u⟩ := cosh19_bounds
  obtain ⟨s1l, s1u⟩ := sinh19_bounds
  obtain ⟨c3l, c3u⟩ := cosh38_bounds
  obtain ⟨s3l, s3u⟩ := sinh38_bounds
  have e1u : Real.cosh 1.9 ^ 2 ≤ 3.4178 ^ 2 :=
    pow_le_pow_left₀ (by linarith) c1u 2
  have e1l : (3.4172 : ℝ) ^ 2 ≤ Real.cosh 1.9 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) c1l 2
  have e2u : Real.sinh 1.9 ^ 2 ≤ 3.2683 ^ 2 :=
    pow_le_pow_left₀ (by linarith) s1u 2
  have e2l : (3.2677 : ℝ) ^ 2 ≤ Real.sinh 1.9 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) s1l 2
  have e3u : Real.cosh 3.8 ^ 2 ≤ 22.367 ^ 2 :=
    pow_le_pow_left₀ (by linarith) c3u 2
  have e3l : (22.356 : ℝ) ^ 2 ≤ Real.cosh 3.8 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) c3l 2
  have e4u : Real.sinh 3.8 ^ 2 ≤ 22.344 ^ 2 :=
    pow_le_pow_left₀ (by linarith) s3u 2
  have e4l : (22.333 : ℝ) ^ 2 ≤ Real.sinh 3.8 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) s3l 2
  constructor <;> linarith

/-- Enclosure for the potential at the witness point. -/
lemma ehV_19_bounds : (-0.271 : ℝ) ≤ ehV 1.9 0 ∧ ehV 1.9 0 ≤ -0.264 := by
  have h : ehV 1.9 0 = ehW1 1.9 + (-1 / 2) := by simp [ehV, ehW2_0]
  rw [h]
  obtain ⟨w1l, w1u⟩ := ehW1_19_bounds
  constructor <;> linarith

/-- Gradient components of the critical Hamiltonian. -/
private def gradH (y : Phase) : Phase :=
  ![y 0 + ehF1 (y 3), y 1 + ehF2 (y 2),
    (y 1 + ehF2 (y 2)) * deriv ehF2 (y 2) + deriv ehW1 (y 2),
    (y 0 + ehF1 (y 3)) * deriv ehF1 (y 3) + deriv ehW2 (y 3)]

/-- The gradient as a continuous linear map. -/
private def gradCLM (y : Phase) : Phase →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun v => gradH y 0 * v 0 + gradH y 1 * v 1
          + gradH y 2 * v 2 + gradH y 3 * v 3,
        map_add' := by intros a b; simp only [Pi.add_apply]; ring,
        map_smul' := by
          intros c a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
    cont := by fun_prop }

/-- Application of the gradient map in explicit components. -/
lemma gradCLM_apply (y v : Phase) : gradCLM y v
    = (y 0 + ehF1 (y 3)) * v 0 + (y 1 + ehF2 (y 2)) * v 1
    + ((y 1 + ehF2 (y 2)) * deriv ehF2 (y 2) + deriv ehW1 (y 2)) * v 2
    + ((y 0 + ehF1 (y 3)) * deriv ehF1 (y 3) + deriv ehW2 (y 3)) * v 3 := rfl

/-- The critical Hamiltonian is differentiable with the gradient above. -/
lemma hasFDerivAt_H (y : Phase) :
    HasFDerivAt ehCriticalHamiltonian (gradCLM y) y := by
  have hfun : ehCriticalHamiltonian = (fun y : Phase =>
      (((y 0 + ehF1 (y 3)) * (y 0 + ehF1 (y 3))
        + (y 1 + ehF2 (y 2)) * (y 1 + ehF2 (y 2))) * 2⁻¹)
      + (ehW1 (y 2) + ehW2 (y 3))) := by
    funext z
    simp only [ehCriticalHamiltonian, ehV, pow_two, div_eq_mul_inv]
  rw [hfun]
  have e0 : HasFDerivAt (fun y : Phase => y 0)
      ((ContinuousLinearMap.proj (0 : Fin 4)) : Phase →L[ℝ] ℝ) y :=
    ((ContinuousLinearMap.proj (0 : Fin 4)) : Phase →L[ℝ] ℝ).hasFDerivAt
  have e1 : HasFDerivAt (fun y : Phase => y 1)
      ((ContinuousLinearMap.proj (1 : Fin 4)) : Phase →L[ℝ] ℝ) y :=
    ((ContinuousLinearMap.proj (1 : Fin 4)) : Phase →L[ℝ] ℝ).hasFDerivAt
  have e2 : HasFDerivAt (fun y : Phase => y 2)
      ((ContinuousLinearMap.proj (2 : Fin 4)) : Phase →L[ℝ] ℝ) y :=
    ((ContinuousLinearMap.proj (2 : Fin 4)) : Phase →L[ℝ] ℝ).hasFDerivAt
  have e3 : HasFDerivAt (fun y : Phase => y 3)
      ((ContinuousLinearMap.proj (3 : Fin 4)) : Phase →L[ℝ] ℝ) y :=
    ((ContinuousLinearMap.proj (3 : Fin 4)) : Phase →L[ℝ] ℝ).hasFDerivAt
  have f1c := HasFDerivAt.comp y (hasDerivAt_ehF1 (y 3)).hasFDerivAt e3
  have f2c := HasFDerivAt.comp y (hasDerivAt_ehF2 (y 2)).hasFDerivAt e2
  have w1c := HasFDerivAt.comp y (hasDerivAt_ehW1 (y 2)).hasFDerivAt e2
  have w2c := HasFDerivAt.comp y (hasDerivAt_ehW2 (y 3)).hasFDerivAt e3
  have u0 := HasFDerivAt.add e0 f1c
  have u0s := HasFDerivAt.mul u0 u0
  have u1 := HasFDerivAt.add e1 f2c
  have u1s := HasFDerivAt.mul u1 u1
  have hsum := HasFDerivAt.add u0s u1s
  have hhalf := HasFDerivAt.mul_const hsum (2⁻¹ : ℝ)
  have w := HasFDerivAt.add w1c w2c
  have hcomb0 := HasFDerivAt.add hhalf w
  have hfun2 : (fun y : Phase =>
      ((((y 0 + ehF1 (y 3)) * (y 0 + ehF1 (y 3))
        + (y 1 + ehF2 (y 2)) * (y 1 + ehF2 (y 2))) * 2⁻¹)
      + (ehW1 (y 2) + ehW2 (y 3))))
      = ((fun y : Phase =>
        ((((fun y : Phase => y 0) + ehF1 ∘ (fun y : Phase => y 3))
          * ((fun y : Phase => y 0) + ehF1 ∘ (fun y : Phase => y 3))
          + ((fun y : Phase => y 1) + ehF2 ∘ (fun y : Phase => y 2))
            * ((fun y : Phase => y 1)
              + ehF2 ∘ (fun y : Phase => y 2))) y * 2⁻¹))
        + ((ehW1 ∘ (fun y : Phase => y 2))
          + ehW2 ∘ (fun y : Phase => y 3))) := by
    funext z
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  have hcomb := hcomb0
  rw [← hfun2] at hcomb
  have hfd : fderiv ℝ (fun y : Phase =>
      ((((y 0 + ehF1 (y 3)) * (y 0 + ehF1 (y 3))
        + (y 1 + ehF2 (y 2)) * (y 1 + ehF2 (y 2))) * 2⁻¹)
      + (ehW1 (y 2) + ehW2 (y 3)))) y = gradCLM y := by
    have h1 := hcomb.fderiv
    rw [h1]
    ext v
    rw [gradCLM_apply, dF1, dF2, dW1, dW2]
    simp only [Pi.add_apply, Function.comp_apply,
      add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.proj_apply,
      smul_apply, smul_eq_mul]
    ring
  have hdiff := hcomb.differentiableAt
  rw [← hfd]
  exact hdiff.hasFDerivAt

/-- The `fderiv` of the critical Hamiltonian is the gradient map. -/
lemma fderiv_H (y : Phase) : fderiv ℝ ehCriticalHamiltonian y = gradCLM y :=
  (hasFDerivAt_H y).fderiv

/-- Lower bound for the `ddF2` factor. -/
lemma ddF2_19_lb : (11.166 : ℝ) ≤ deriv (deriv ehF2) 1.9 := by
  have h : deriv (deriv ehF2) 1.9 = Real.sinh 3.8 / 2 := by simp [ddF2_19, h3819]
  rw [h]
  linarith [sinh38_bounds.1]

/-- The momentum coordinate making the Hamiltonian vanish. -/
private def witS : ℝ := Real.sqrt (-2 * ehV 1.9 0)

/-- The witness point. -/
private def wit : Phase := ![0, witS - ehF2 1.9, 1.9, 0]

/-- Coordinates of the witness and of the test direction. -/
lemma w0 : wit 0 = 0 := by simp [wit]

lemma w1 : wit 1 = witS - ehF2 1.9 := by simp [wit]

lemma w2 : wit 2 = 1.9 := by simp [wit]

lemma w3 : wit 3 = 0 := by simp [wit]

lemma e10 : (![0, 1, 0, 0] : Phase) 0 = 0 := by simp

lemma e11 : (![0, 1, 0, 0] : Phase) 1 = 1 := by simp

lemma e12 : (![0, 1, 0, 0] : Phase) 2 = 0 := by simp

lemma e13 : (![0, 1, 0, 0] : Phase) 3 = 0 := by simp

/-- Enclosure for the witness momentum. -/
lemma witS_bounds : (0.72 : ℝ) ≤ witS ∧ witS ≤ 0.74 := by
  obtain ⟨vl, vu⟩ := ehV_19_bounds
  have hR2lo : (0.72 : ℝ) ^ 2 ≤ -2 * ehV 1.9 0 := by linarith [vu]
  have hR2hi : -2 * ehV 1.9 0 ≤ (0.74 : ℝ) ^ 2 := by linarith [vl]
  constructor
  · have h : (0.72 : ℝ) ≤ Real.sqrt (-2 * ehV 1.9 0) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0.72)]
      exact Real.sqrt_le_sqrt hR2lo
    simpa [witS] using h
  · have h : Real.sqrt (-2 * ehV 1.9 0) ≤ 0.74 := by
      have hle := Real.sqrt_le_sqrt hR2hi
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0.74)] at hle
    simpa [witS] using h

/-- The witness lies on the zero level. -/
lemma wit_H0 : ehCriticalHamiltonian wit = 0 := by
  obtain ⟨vl, vu⟩ := ehV_19_bounds
  have hR2nn : (0 : ℝ) ≤ -2 * ehV 1.9 0 := by linarith [vu]
  have hsq : witS ^ 2 = -2 * ehV 1.9 0 := Real.sq_sqrt hR2nn
  have hbb : (witS - ehF2 1.9) + ehF2 1.9 = witS := by ring
  have hV : ehV 1.9 0 = ehW1 1.9 + (-1 / 2) := by simp [ehV, ehW2_0]
  simp only [ehCriticalHamiltonian, ehV, w0, w1, w2, w3, ehF1_0, ehW2_0]
  rw [hbb, hsq]
  linarith [hV]

/-- The radial derivative at the witness is negative. -/
lemma wit_fderiv_neg : fderiv ℝ ehCriticalHamiltonian wit wit < 0 := by
  have hS := witS_bounds
  have hF := ehF2_19_lb
  have hSP := dF2_19_ub
  have hSPnn : (0 : ℝ) ≤ deriv ehF2 1.9 := by
    have h : deriv ehF2 1.9 = Real.cosh 3.8 / 4 := by simp [dF2, h3819]
    rw [h]
    linarith [cosh38_bounds.1]
  have hDW := dW1_19_bounds.2
  have p1 : (0 : ℝ) ≤ (witS - 0.72) * (ehF2 1.9 - witS) :=
    mul_nonneg (by linarith [hS.1]) (by linarith [hS.2, hF])
  have pa : witS * (witS - ehF2 1.9) ≤ 0.72 * (0.74 - 2.791) := by
    nlinarith [p1, hS.1, hS.2, hF]
  have p2 : (0 : ℝ) ≤ (0.74 - witS) * deriv ehF2 1.9 :=
    mul_nonneg (by linarith [hS.2]) hSPnn
  have pb : witS * deriv ehF2 1.9 + deriv ehW1 1.9 ≤ 0.74 * 5.59175 - 6.06 := by
    nlinarith [p2, hS.2, hSP, hDW]
  rw [fderiv_H, gradCLM_apply, w0, w1, w2, w3, ehF1_0, dW2_0]
  nlinarith [pa, pb]

/-- The witness has nonzero derivative. -/
lemma wit_fderiv_ne : fderiv ℝ ehCriticalHamiltonian wit ≠ 0 := by
  intro hcon
  have hbb : (witS - ehF2 1.9) + ehF2 1.9 = witS := by ring
  have h1 : (fderiv ℝ ehCriticalHamiltonian wit) ![0, 1, 0, 0] = witS := by
    rw [fderiv_H, gradCLM_apply, w0, w1, w2, w3, e10, e11, e12, e13,
      ehF1_0, dW2_0, hbb]
    ring
  rw [hcon] at h1
  simp at h1
  linarith [witS_bounds.1]

/-- The determinant stays positive at the witness, uniformly in the angle. -/
lemma wit_detUW (s t : ℝ) (hst : s ^ 2 + t ^ 2 = 1) :
    (8 : ℝ) < ehDetUW s t (wit 2) (wit 3) := by
  rw [w2, w3]
  have hR2 : ehR2 1.9 0 = -2 * ehV 1.9 0 := rfl
  obtain ⟨vl, vu⟩ := ehV_19_bounds
  have hR2nn : (0 : ℝ) ≤ ehR2 1.9 0 := by linarith [hR2, vu]
  have hR2ub : ehR2 1.9 0 ≤ 0.542 := by linarith [hR2, vl]
  have hr0 : (0 : ℝ) ≤ Real.sqrt (ehR2 1.9 0) := Real.sqrt_nonneg _
  have hr74 : Real.sqrt (ehR2 1.9 0) ≤ 0.74 := by
    have hle : ehR2 1.9 0 ≤ (0.74 : ℝ) ^ 2 := by linarith [hR2ub]
    calc Real.sqrt (ehR2 1.9 0) ≤ Real.sqrt ((0.74 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = 0.74 := Real.sqrt_sq (by norm_num)
  have hDs : ehDs s 1.9 0 = 15 / 16 := by
    simp only [ehDs, ddF1_0, ddW2_0]
    ring
  have hdet : ehDetUW s t 1.9 0
      = ehDs s 1.9 0 * (deriv ehW1 1.9 ^ 2
          + ehR2 1.9 0 * ehCt t 1.9 0)
        + ehCt t 1.9 0 * deriv ehW2 0 ^ 2 := rfl
  have hCt_eq : ehCt t 1.9 0 = Real.sqrt (ehR2 1.9 0) * t
      * deriv (deriv ehF2) 1.9 + deriv (deriv ehW1) 1.9 := rfl
  have hS2nn : (0 : ℝ) ≤ deriv (deriv ehF2) 1.9 := by
    linarith [ddF2_19_lb]
  have ht : (-1 : ℝ) ≤ t := by
    nlinarith [hst, sq_nonneg s, sq_nonneg (t + 1)]
  have e1 : Real.sqrt (ehR2 1.9 0) * (-1) * deriv (deriv ehF2) 1.9
      ≤ Real.sqrt (ehR2 1.9 0) * t * deriv (deriv ehF2) 1.9 := by
    have hpos : (0 : ℝ) ≤ (t + 1)
        * (Real.sqrt (ehR2 1.9 0) * deriv (deriv ehF2) 1.9) :=
      mul_nonneg (by linarith)
        (mul_nonneg hr0 hS2nn)
    linarith [hpos]
  have e2 : Real.sqrt (ehR2 1.9 0) * (-1) * deriv (deriv ehF2) 1.9
      ≥ -(0.74 * 11.173) := by
    have hle : Real.sqrt (ehR2 1.9 0) * deriv (deriv ehF2) 1.9
        ≤ 0.74 * 11.173 :=
      mul_le_mul hr74 ddF2_19_ub hS2nn (by norm_num)
    linarith [hle]
  have hCt_lo : ehCt t 1.9 0 ≥ -(0.74 * 11.173) - 41.83 := by
    rw [hCt_eq]
    linarith [e1, e2, ddW1_19_bounds.1]
  have hDWsq : deriv ehW1 1.9 ^ 2 ≥ 6.06 ^ 2 := by
    nlinarith [dW1_19_bounds.2, sq_nonneg (deriv ehW1 1.9 + 6.06)]
  have e3 : ehR2 1.9 0 * ehCt t 1.9 0
      ≥ 0.542 * (-(0.74 * 11.173) - 41.83) := by
    have g1 : ehR2 1.9 0 * ehCt t 1.9 0
        ≥ ehR2 1.9 0 * (-(0.74 * 11.173) - 41.83) :=
      mul_le_mul_of_nonneg_left hCt_lo hR2nn
    have g2 : ehR2 1.9 0 * (-(0.74 * 11.173) - 41.83)
        ≥ 0.542 * (-(0.74 * 11.173) - 41.83) :=
      mul_le_mul_of_nonpos_right hR2ub (by norm_num)
    linarith [g1, g2]
  rw [hdet, hDs, dW2_0]
  linarith [hDWsq, e3]

/-- The witness lies in the estimate region. -/
lemma wit_mem : wit ∈ ehEstimateRegion := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w2]; norm_num
  · rw [w3]
  · rw [w3]
    exact div_nonneg (le_of_lt Real.pi_pos) (by norm_num)
  · rw [w2, w3]
    linarith [ehV_19_bounds.2]
  · left
    rw [w2]
    norm_num
  · exact wit_H0
  · exact wit_fderiv_ne
  · intro s t hst
    have h8 := wit_detUW s t hst
    linarith [h8]

end

end BirkhoffGlobalSection

open BirkhoffGlobalSection

/-- Disproof of radial positivity: the witness is in the region but the
radial derivative is negative. -/
theorem solution :
    ¬ ∀ y : Phase, y ∈ ehEstimateRegion
      → 0 < fderiv ℝ ehCriticalHamiltonian y y := by
  intro h
  have hpos := h wit wit_mem
  have hneg := wit_fderiv_neg
  linarith [hpos, hneg]
