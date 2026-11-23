-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderIntegralFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:34.218539+00:00
-- url     : https://prove2.me/submissions/cd27334d-2443-45e1-acca-35b4df818702

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
private theorem sum_Icc_eq_mul_sum_div_sub_sum_partial (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, c n = (N : ℂ) * (∑ n ∈ Icc 1 N, c n / (n : ℂ))
      - ∑ k ∈ range N, ∑ n ∈ Icc 1 k, c n / (n : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), Finset.sum_Icc_succ_top (Nat.le_add_left 1 N),
      Finset.sum_range_succ, ih]
    have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have e : ((N : ℂ) + 1) * (c (N + 1) / ((N : ℂ) + 1)) = c (N + 1) := by field_simp
    push_cast
    linear_combination -e
private lemma kronecker_tendsto_zero (c : ℕ → ℂ) (S : ℂ)
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, c n / (n : ℂ)) atTop (𝓝 S)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, c n) / (N : ℂ)) atTop (𝓝 0) := by
  have hc := h.cesaro_smul
  have hd := h.sub hc
  rw [sub_self] at hd
  refine hd.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sum_Icc_eq_mul_sum_div_sub_sum_partial c N, Complex.real_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : (N : ℂ) * (∑ n ∈ Icc 1 N, c n / (n : ℂ)) / (N : ℂ) = ∑ n ∈ Icc 1 N, c n / (n : ℂ) := by
    field_simp
  push_cast
  linear_combination -e
private lemma kronecker_tendsto_zero_real (c : ℕ → ℂ) (S : ℂ)
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, c n / (n : ℂ)) atTop (𝓝 S)) :
    Tendsto (fun U : ℝ => (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)) atTop (𝓝 0) := by
  have h0 := (kronecker_tendsto_zero c S h).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h1 : Tendsto (fun U : ℝ => ((⌊U⌋₊ : ℝ) / U : ℝ)) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have h2 : Tendsto (fun U : ℝ => ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp h1
  have h3 := h0.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
  show (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (⌊U⌋₊ : ℂ) * ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ) =
    (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)
  have hf1 : 1 ≤ ⌊U⌋₊ := (Nat.one_le_floor_iff U).mpr hU
  have hf : (⌊U⌋₊ : ℂ) ≠ 0 := by exact_mod_cast (show ⌊U⌋₊ ≠ 0 by omega)
  have e : (⌊U⌋₊ : ℂ) * ((⌊U⌋₊ : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hf
  push_cast
  linear_combination ((∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)) * e
end Formalism.HermitianLattices.GL2PrimeSums
end

set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution : SmoothedRemainderIntegralFormula := by
  intro a S h y hy
  refine ⟨S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ), ?_, ?_⟩
  · have hlim : Tendsto (fun U : ℝ => (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℂ))
          - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / (U : ℂ)
          + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) atTop
        (𝓝 (S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - 0 + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ))) :=
      (((h.comp (tendsto_nat_floor_atTop (α := ℝ))).sub_const _).sub
        (kronecker_tendsto_zero_real a S h)).add_const _
    rw [sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop y] with U hU
    exact (integral_partial_sum_div_sq a hy hU).symm
  · have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < y by linarith).ne'
    have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) =
        (y : ℂ) * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    have e : (y : ℂ) * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      field_simp
    unfold Gchi
    rw [hsum]
    linear_combination e
end Formalism.HermitianLattices.GL2PrimeSums
