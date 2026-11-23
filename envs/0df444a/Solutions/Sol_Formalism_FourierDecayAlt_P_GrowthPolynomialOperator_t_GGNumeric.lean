-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_GGNumeric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:41.280885+00:00
-- url     : https://prove2.me/submissions/3babc6f1-32a9-428d-a118-b95c5a08cdbe

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_euler_product_bounds

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
theorem _root_.solution : GGNumeric := by
  intro k g hg
  have hg0 : 0 < g := by linarith
  have hx0 : 0 < g⁻¹ := inv_pos.mpr hg0
  have hgx : g⁻¹ * g = 1 := inv_mul_cancel₀ hg0.ne'
  have hx3 : g⁻¹ ≤ 1 / 3 := by nlinarith [mul_le_mul_of_nonneg_left hg hx0.le]
  have hprod : ∏ i ∈ Icc 1 k, (1 - (g ^ i)⁻¹)⁻¹ = (∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i))⁻¹ := by
    rw [Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [inv_pow]
  have e3 : (3:ℝ) / g = 3 * g⁻¹ := div_eq_mul_inv 3 g
  rw [hprod, e3]
  obtain ⟨h1, -⟩ := euler_product_bounds g⁻¹ hx0 hx3 k
  have hpos : 0 < 1 - 3 / 2 * g⁻¹ := by linarith
  have hP : 1 - 3 / 2 * g⁻¹ ≤ ∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i) := by
    have := pow_nonneg hx0.le (k + 1)
    linarith
  have hab : 1 ≤ (1 - 3 / 2 * g⁻¹) * (1 + 3 * g⁻¹) := by
    nlinarith [mul_nonneg hx0.le (show (0:ℝ) ≤ 1 / 3 - g⁻¹ by linarith)]
  calc (∏ i ∈ Icc 1 k, (1 - g⁻¹ ^ i))⁻¹ ≤ (1 - 3 / 2 * g⁻¹)⁻¹ := by
        first
          | exact inv_anti₀ hpos hP
          | exact inv_le_inv_of_le hpos hP
    _ = (1 - 3 / 2 * g⁻¹)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (1 - 3 / 2 * g⁻¹)⁻¹ * ((1 - 3 / 2 * g⁻¹) * (1 + 3 * g⁻¹)) :=
        mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hpos.le)
    _ = 1 + 3 * g⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
