-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderRealIntegralFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:34.349268+00:00
-- url     : https://prove2.me/submissions/6c85acc0-78a5-4db1-a419-a33da93b3904

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmoothedRemainderRealIntegralFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Filter Topology MeasureTheory
namespace Formalism.HermitianLattices.GL2PrimeSums
section abel
variable {𝕜 : Type*} [RCLike 𝕜]
private lemma hasDerivAt_inv_coe (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => ((u : 𝕜))⁻¹) (-((t : 𝕜) ^ 2)⁻¹) t := by
  have h := (RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_inv ht)
  have hfun : (fun u : ℝ => ((u : 𝕜))⁻¹) = (RCLike.ofRealCLM (K := 𝕜)) ∘ fun y : ℝ => y⁻¹ := by
    funext u
    simp
  rw [hfun]
  exact h.congr_deriv (by simp)
private lemma Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega
private theorem continuousOn_inv_sq_Icc_of_pos {y U : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) := by
  refine ContinuousOn.inv₀ ((RCLike.continuous_ofReal (K := 𝕜)).pow 2).continuousOn ?_
  intro t ht
  have : (t : 𝕜) ≠ 0 := by
    rw [Ne, RCLike.ofReal_eq_zero]
    exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
  exact pow_ne_zero 2 this
private lemma integrableOn_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2) (Set.Icc y U) := by
  have hg : IntegrableOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) :=
    (continuousOn_inv_sq_Icc_of_pos (by linarith)).integrableOn_Icc
  have := integrableOn_mul_sum_Icc c (m := 1) (by linarith : (0 : ℝ) ≤ y) hg
  refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [div_eq_inv_mul]
private theorem sum_Icc_zero_ite_eq_sum_Icc_one (c : ℕ → 𝕜) (N : ℕ) :
    ∑ k ∈ Icc 0 N, (if k = 0 then (0 : 𝕜) else c k) = ∑ k ∈ Icc 1 N, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, Icc_one_eq_Ioc_zero]
  simp only [↓reduceIte, zero_add]
  exact Finset.sum_congr rfl fun k hk => if_neg (Finset.mem_Ioc.mp hk).1.ne'
private lemma integral_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : 𝕜) + (∑ n ∈ Icc 1 ⌊y⌋₊, c n) / (y : 𝕜) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hne : ∀ t ∈ Set.Icc y U, t ≠ 0 := fun t ht => (show (0 : ℝ) < t by linarith [ht.1]).ne'
  have hf_diff : ∀ t ∈ Set.Icc y U, DifferentiableAt ℝ (fun u : ℝ => ((u : 𝕜))⁻¹) t :=
    fun t ht => (hasDerivAt_inv_coe t (hne t ht)).differentiableAt
  have hf_int : IntegrableOn (deriv (fun u : ℝ => ((u : 𝕜))⁻¹)) (Set.Icc y U) := by
    refine ((continuousOn_inv_sq_Icc_of_pos (𝕜 := 𝕜) (U := U) (by linarith)).neg.integrableOn_Icc).congr_fun
      (fun t ht => ?_) measurableSet_Icc
    exact ((hasDerivAt_inv_coe t (hne t ht)).deriv).symm
  have key : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      ((U : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊U⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ((y : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊y⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
            ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) :=
    sum_mul_eq_sub_sub_integral_mul (fun n => if n = 0 then (0 : 𝕜) else c n) hy0 hU hf_diff hf_int
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜)) := by
    calc ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k)
        = ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, c k / (k : 𝕜) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk0 : k ≠ 0 := (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1).ne'
          rw [if_neg hk0, RCLike.ofReal_natCast]
          ring
      _ = _ := by
          rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero]
          exact eq_sub_of_add_eq' (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hU))
  have hint_r : ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) =
      -∫ t in Set.Ioc y U, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / (t : 𝕜) ^ 2 := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith [ht.1]).ne'
    simp only [(hasDerivAt_inv_coe (𝕜 := 𝕜) t ht0).deriv, sum_Icc_zero_ite_eq_sum_Icc_one]
    ring
  rw [intervalIntegral.integral_of_le hU]
  linear_combination -key + hL + hint_r - ((U : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊U⌋₊
    + ((y : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊y⌋₊
end abel
private theorem integral_psumR_sub_div_sq_eq_partial_sums (a : ℕ → ℝ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, (psumR a u - u) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y
        - (Real.log U - Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hU0 : 0 < U := by linarith
  have hsplit : (fun u : ℝ => (psumR a u - u) / u ^ 2) =
      fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 - u⁻¹ := by
    funext u
    rw [sub_div, psumR]
    congr 1
    rcases eq_or_ne u 0 with h | h
    · simp [h]
    · rw [pow_two, div_mul_eq_div_div, div_self h, one_div]
  have hA : IntervalIntegrable (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2) volume y U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).mpr
      (integrableOn_partial_sum_div_sq (𝕜 := ℝ) a hy)
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume y U := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun x hx => ?_)
    rw [Set.uIcc_of_le hU] at hx
    exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
  have hA_eq : ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y :=
    integral_partial_sum_div_sq (𝕜 := ℝ) a hy hU
  rw [hsplit, intervalIntegral.integral_sub hA hinv, integral_inv_of_pos hy0 hU0,
    Real.log_div hU0.ne' hy0.ne', hA_eq]
end Formalism.HermitianLattices.GL2PrimeSums
end

set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution : SmoothedRemainderRealIntegralFormula := by
  intro a h y hy
  refine ⟨-1 - Real.eulerMascheroniConstant + (-(∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
    + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y + Real.log y), (h.add_const _).congr' ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop y] with U hU
    rw [integral_psumR_sub_div_sq_eq_partial_sums a hy hU, integral_psumR_sub_div_sq_eq_partial_sums a le_rfl (hy.trans hU)]
    simp only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one,
      Real.log_one]
    ring
  · have hy0 : y ≠ 0 := (show (0 : ℝ) < y by linarith).ne'
    have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) =
        y * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have e : y * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      field_simp
    unfold Gone
    rw [hsum]
    linear_combination e
end Formalism.HermitianLattices.GL2PrimeSums
