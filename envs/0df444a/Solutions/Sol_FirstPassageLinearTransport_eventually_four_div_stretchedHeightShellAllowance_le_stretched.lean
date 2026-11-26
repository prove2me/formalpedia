-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_four_div_stretchedHeightShellAllowance_le_stretched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:41.728593+00:00
-- url     : https://prove2.me/submissions/937ea1f0-4f3a-41f6-b706-5cbb9d4fe350

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_QuantitativeDensity_stretchedShellScale_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {zeta alpha sigma : ℝ} (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigmaAlpha : sigma ≤ alpha) :
    ∀ᶠ M : ℕ in atTop,
      4 / stretchedHeightShellAllowance zeta alpha M ≤
        4 * Real.exp
          (-(zeta * (Real.log 2 / 2) ^ alpha) *
            (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with M hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase0 : 0 ≤ Real.log 2 / 2 := (div_pos hlog2 (by norm_num)).le
  have hshift0 : 0 ≤ QuantitativeDensity.stretchedShellScale M :=
    (QuantitativeDensity.stretchedShellScale_pos M).le
  have hM0 : 0 ≤ (M : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg M) hlog2.le
  have hbase :
      (Real.log 2 / 2) * QuantitativeDensity.stretchedShellScale M ≤
        (M : ℝ) * Real.log 2 := by
    unfold QuantitativeDensity.stretchedShellScale
    have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hpow := Real.rpow_le_rpow
    (mul_nonneg hbase0 hshift0) hbase halpha0.le
  rw [Real.mul_rpow hbase0 hshift0] at hpow
  have hscaleOne : 1 ≤ QuantitativeDensity.stretchedShellScale M := by
    unfold QuantitativeDensity.stretchedShellScale
    have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hpowCompare :
      (QuantitativeDensity.stretchedShellScale M) ^ sigma ≤
        (QuantitativeDensity.stretchedShellScale M) ^ alpha := by
    exact Real.rpow_le_rpow_of_exponent_le hscaleOne hsigmaAlpha
  have hcoeff0 : 0 ≤ (Real.log 2 / 2) ^ alpha :=
    Real.rpow_nonneg hbase0 _
  have hpowSigma :
      (Real.log 2 / 2) ^ alpha *
          (QuantitativeDensity.stretchedShellScale M) ^ sigma ≤
        ((M : ℝ) * Real.log 2) ^ alpha := by
    exact (mul_le_mul_of_nonneg_left hpowCompare hcoeff0).trans hpow
  have hexp :
      Real.exp (-(zeta * (((M : ℝ) * Real.log 2) ^ alpha))) ≤
        Real.exp
          (-(zeta * (Real.log 2 / 2) ^ alpha) *
            (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
    apply Real.exp_le_exp.2
    nlinarith
  unfold stretchedHeightShellAllowance
  rw [div_eq_mul_inv, ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_left hexp (by norm_num)
end FirstPassageLinearTransport
