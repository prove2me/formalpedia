-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.LowZeroReciprocal
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:32:33.442385+00:00
-- url     : https://prove2.me/submissions/b30dd665-1a90-466c-92a1-929462e16e39

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterCount
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterAbel
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_RationalLogCertificates

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set MeasureTheory
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem positive_zero_height_fourteen : ∀ (ρ : ℂ)
    (hρ : DusartSmoothing.RvM.IsNontrivialZero ρ) (hi : 0 < ρ.im),
    14 < ρ.im :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterCount.1

private theorem finite_count_integrable : ∀ (Z : Finset ℂ) (a b : ℝ),
    IntervalIntegrable (finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im) volume a b :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel.1

private theorem log_add_five_upper : ∀ (t : ℝ) (ht : 14 ≤ t),
    Real.log (t + 5) ≤ Real.log t + 1 / 3 :=
  ExplicitPNT.DusartTable1.Modules.RationalLogCertificates.2.2.2

private theorem finite_positive_reciprocal_log_bound (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 14 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      (Real.log (T / (2 * Real.pi)))^2 / (4 * Real.pi) - 1 / (4 * Real.pi) +
        (9 * Real.log 14 + 91) / 14 := by
  have hT0 : 0 < T := by linarith
  let k : ℝ := 1 / (2 * Real.pi)
  let c : ℝ := Real.log (2 * Real.pi) + 1
  let g : ℝ → ℝ := fun t => 1 / t
  let d : ℝ → ℝ := fun t => -1 / t^2
  let W : ℝ → ℝ := fun t => k * t * (Real.log t - c) + 9 * Real.log t + 82
  let J : ℝ → ℝ := fun t =>
    -(k / 2) * (Real.log t - c)^2 + (9 * Real.log t + 91) / t
  have hk : 0 < k := by dsimp [k]; positivity
  have hcont : ContinuousOn d (Icc 14 T) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    dsimp [d]
    fun_prop (disch := positivity)
  have hW : ContinuousOn W (Icc 14 T) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    dsimp [W]
    fun_prop (disch := positivity)
  have hd : ∀ t ∈ Icc 14 T, HasDerivAt g (d t) t := by
    intro t ht
    have hn : t ≠ 0 := by linarith [ht.1]
    have hh := (hasDerivAt_id t).inv hn
    have he : (id : ℝ → ℝ)⁻¹ = g := by funext u; simp [g]
    rw [he] at hh
    simpa only [d, id_eq] using hh
  have hJ : ∀ t ∈ uIcc 14 T, HasDerivAt J (W t * d t) t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have hn : t ≠ 0 := by linarith [ht.1]
    have h1 := (((Real.hasDerivAt_log hn).sub_const c).pow 2).const_mul (-(k / 2))
    have h2 := (((Real.hasDerivAt_log hn).const_mul 9).add_const 91).div
      (hasDerivAt_id t) hn
    apply (h1.add h2).congr_deriv
    dsimp [W, d]
    field_simp [hn]
    ring
  have hcount : ∀ t ∈ Icc 14 T,
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ W t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hc := finite_actual_zero_count_bound Z hZ t (by linarith [ht.1])
    have hl := log_add_five_upper t ht.1
    have he : DusartSmoothing.RvM.countingMain t =
        k * t * (Real.log t - c) := by
      unfold DusartSmoothing.RvM.countingMain
      rw [Real.log_div ht0.ne' (by positivity)]
      dsimp [k, c]
      ring
    rw [he] at hc
    dsimp [W]
    linarith only [hc, hl]
  have hi : IntervalIntegrable
      (fun t => finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t) volume 14 T :=
    (finite_count_integrable Z 14 T).mul_continuousOn (by simpa [uIcc_of_le hT] using hcont)
  have hcW : ContinuousOn (fun t => W t * d t) (uIcc 14 T) := by
    rw [uIcc_of_le hT]
    intro t ht
    exact (hW t ht).mul (hcont t ht)
  have himaj : IntervalIntegrable (fun t => W t * d t) volume 14 T := hcW.intervalIntegrable
  have hile : (∫ t in 14..T, W t * d t) ≤
      ∫ t in 14..T, finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t := by
    apply intervalIntegral.integral_mono_on hT himaj hi
    intro t ht
    apply mul_le_mul_of_nonpos_right (hcount t ht)
    dsimp [d]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have hival : (∫ t in 14..T, W t * d t) = J T - J 14 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hJ himaj
  have hQ : finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im T =
      ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp [primeStep, hγ ρ hρ]
  have hcb := hcount T ⟨hT, le_rfl⟩
  rw [hQ] at hcb
  have hterm := mul_le_mul_of_nonneg_left hcb (show 0 ≤ g T by dsimp [g]; positivity)
  have he := finite_zero_summation_by_parts Z DusartSmoothing.RvM.zeroMult Complex.im
    14 T hT (fun ρ hρ => ⟨(positive_zero_height_fourteen ρ
      (hZ ρ hρ).1 (hZ ρ hρ).2).le, hγ ρ hρ⟩) g d hcont hd
  have hsum : (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      g T * W T - J T + J 14 := by
    change (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ _
    rw [he]
    rw [hival] at hile
    linarith only [hile, hterm]
  have hend : g T * W T - J T + J 14 =
      (Real.log (T / (2 * Real.pi)))^2 / (4 * Real.pi) - 1 / (4 * Real.pi) +
      (9 * Real.log 14 + 91) / 14 - 9 / T -
        (k / 2) * (Real.log 14 - c)^2 := by
    dsimp [g, W, J, k, c]
    rw [Real.log_div hT0.ne' (by positivity)]
    field_simp [hT0.ne', Real.pi_ne_zero]
    ring
  rw [hend] at hsum
  have hn1 : 0 ≤ 9 / T := by positivity
  have hn2 : 0 ≤ (k / 2) * (Real.log 14 - c)^2 := by positivity
  linarith only [hsum, hn1, hn2]

end ExplicitPNT.DusartTable1

theorem solution :
∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 14 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      (Real.log (T / (2 * Real.pi)))^2 / (4 * Real.pi) - 1 / (4 * Real.pi) +
        (9 * Real.log 14 + 91) / 14 := by
  exact finite_positive_reciprocal_log_bound
