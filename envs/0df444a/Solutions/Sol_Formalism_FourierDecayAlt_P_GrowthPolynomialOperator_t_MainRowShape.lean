-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_MainRowShape
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:33.855946+00:00
-- url     : https://prove2.me/submissions/8b2908b8-cd39-413e-ae03-0386024be2dc

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
open Formalism.FourierDecayAlt.PB
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : MainRowShape := by
  intro δ y z hδ hy hz h1
  have hx0 : 0 ≤ δ + y + z := by linarith
  have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (show (0:ℝ) ≤ 1 - (δ + y + z) by linarith) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hconv
  have he := Real.exp_one_lt_d9
  have hδe : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
  have hprod : (1 + δ) * Real.exp y * Real.exp z ≤ Real.exp (δ + y + z) := by
    rw [Real.exp_add, Real.exp_add, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hδe (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left he.le hx0]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
