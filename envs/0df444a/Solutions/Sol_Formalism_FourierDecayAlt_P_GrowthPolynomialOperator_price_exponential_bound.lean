-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.price_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:33.590557+00:00
-- url     : https://prove2.me/submissions/ec274394-b824-4f2b-96ab-7c377a14d672

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution (f k : ℕ) (b g : ℝ) (hb : 1 ≤ b) (hk : 1 ≤ k) (hf : f ≤ k)
    (hg : ((k : ℝ) * b) ^ 8 ≤ g) :
    0 < g ∧ (f : ℝ) / g ≤ (b ^ 7)⁻¹ ∧ 0 ≤ (1 + 3 / g) ^ f ∧
      (1 + 3 / g) ^ f ≤ Real.exp (3 * (b ^ 7)⁻¹) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hfk : (f:ℝ) ≤ k := by exact_mod_cast hf
  have hb0 : 0 < b := by linarith
  have hkb : b ≤ k * b := by nlinarith
  have hkb' : (k:ℝ) ≤ k * b := by nlinarith
  have hkb0 : 0 ≤ (k:ℝ) * b := by linarith
  have h7 : b ^ 7 ≤ (k * b) ^ 7 := pow_le_pow_left₀ hb0.le hkb 7
  have hb7 : 0 < b ^ 7 := pow_pos hb0 7
  have hb71 : (1:ℝ) ≤ b ^ 7 := by
    have := pow_le_pow_left₀ zero_le_one hb 7
    simpa using this
  have e8 : ((k:ℝ) * b) ^ 8 = (k * b) ^ 7 * (k * b) := by ring
  have hk8 : (k:ℝ) * b ^ 7 ≤ (k * b) ^ 8 := by
    nlinarith [mul_le_mul h7 hkb' (by linarith) (pow_nonneg hkb0 7)]
  have hkb7 : b ^ 7 ≤ (k:ℝ) * b ^ 7 := by nlinarith [mul_le_mul_of_nonneg_right hkR hb7.le]
  have hg0 : 0 < g := by linarith
  have hfg : (f:ℝ) * b ^ 7 ≤ g := by
    have := mul_le_mul_of_nonneg_right hfk hb7.le
    linarith
  have hfb : (f:ℝ) ≤ (b ^ 7)⁻¹ * g := by
    calc (f:ℝ) = (f * b ^ 7) * (b ^ 7)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hb7.ne', mul_one]
      _ ≤ g * (b ^ 7)⁻¹ := mul_le_mul_of_nonneg_right hfg (inv_nonneg.mpr hb7.le)
      _ = (b ^ 7)⁻¹ * g := mul_comm _ _
  have hdiv : (f:ℝ) / g ≤ (b ^ 7)⁻¹ := by
    first
      | exact (div_le_iff₀ hg0).mpr hfb
      | exact (div_le_iff hg0).mpr hfb
  have hpos0 : 0 ≤ 1 + 3 / g := by
    have := div_pos (show (0:ℝ) < 3 by norm_num) hg0
    linarith
  have h1 : 1 + 3 / g ≤ Real.exp (3 / g) := by linarith [Real.add_one_le_exp (3 / g)]
  have h2 : (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := pow_le_pow_left₀ hpos0 h1 f
  rw [← Real.exp_nat_mul] at h2
  have h3 : (f:ℝ) * (3 / g) ≤ 3 * (b ^ 7)⁻¹ := by
    have : (f:ℝ) * (3 / g) = 3 * (f / g) := by ring
    rw [this]
    linarith
  exact ⟨hg0, hdiv, pow_nonneg hpos0 f, h2.trans (Real.exp_le_exp.mpr h3)⟩
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
