-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.ZeroSumPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:30:37.169387+00:00
-- url     : https://prove2.me/submissions/3e9cf074-e5fb-4d91-b994-cfc2bb7196b8

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PsiComparison
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterAbel

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set MeasureTheory
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_count_integrable : ∀ (Z : Finset ℂ) (a b : ℝ),
    IntervalIntegrable (finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im) volume a b :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel.1

private theorem finite_zero_sum_le_primitive (Z : Finset ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im ∧ ρ.im ≤ b)
    (g d W J : ℝ → ℝ)
    (hcont : ContinuousOn d (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (d t) t)
    (hJ : ∀ t ∈ uIcc a b, HasDerivAt J (W t * d t) t)
    (hneg : ∀ t ∈ Icc a b, d t ≤ 0)
    (hcount : ∀ t ∈ Icc a b,
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ W t)
    (hg : 0 ≤ g b) (hend : g b * W b ≤ J b) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ J a := by
  have hi : IntervalIntegrable
      (fun t => finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t) volume a b :=
    (finite_count_integrable Z a b).mul_continuousOn (by simpa [uIcc_of_le hab] using hcont)
  have hcW : ContinuousOn (fun t => W t * d t) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro t ht
    exact (hW t ht).mul (hcont t ht)
  have himaj : IntervalIntegrable (fun t => W t * d t) volume a b := hcW.intervalIntegrable
  have hile : (∫ t in a..b, W t * d t) ≤
      ∫ t in a..b, finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t := by
    exact intervalIntegral.integral_mono_on hab himaj hi
      (fun t ht => mul_le_mul_of_nonpos_right (hcount t ht) (hneg t ht))
  have hival : (∫ t in a..b, W t * d t) = J b - J a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hJ himaj
  have hQb : finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im b =
      ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp [primeStep, (hγ ρ hρ).2]
  have hcb := hcount b ⟨hab, le_rfl⟩
  rw [hQb] at hcb
  have hterm := (mul_le_mul_of_nonneg_left hcb hg).trans hend
  have he := finite_zero_summation_by_parts Z DusartSmoothing.RvM.zeroMult Complex.im
    a b hab hγ g d hcont hd
  rw [he]
  rw [hival] at hile
  linarith only [hile, hterm]

end ExplicitPNT.DusartTable1

theorem solution :
∀ (Z : Finset ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im ∧ ρ.im ≤ b)
    (g d W J : ℝ → ℝ)
    (hcont : ContinuousOn d (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (d t) t)
    (hJ : ∀ t ∈ uIcc a b, HasDerivAt J (W t * d t) t)
    (hneg : ∀ t ∈ Icc a b, d t ≤ 0)
    (hcount : ∀ t ∈ Icc a b,
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ W t)
    (hg : 0 ≤ g b) (hend : g b * W b ≤ J b),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ J a := by
  exact finite_zero_sum_le_primitive
