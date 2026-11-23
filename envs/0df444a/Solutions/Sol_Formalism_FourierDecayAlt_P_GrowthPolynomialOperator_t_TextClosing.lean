-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_TextClosing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:16.895828+00:00
-- url     : https://prove2.me/submissions/c36c3472-89ec-4411-8a62-e9f179dce75f

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
theorem _root_.solution : NormSqAddBoundBySqrtSum := by
  intro H _ x y η ε dd hdd hx hy
  have hx' : ‖x‖ ≤ √(1 + η + ε) * √dd := by
    rw [← Real.sqrt_mul' _ hdd]
    calc ‖x‖ = √(‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ √((1 + η + ε) * dd) := Real.sqrt_le_sqrt hx
  have hy' : ‖y‖ ≤ √ε * √dd := by
    rw [← Real.sqrt_mul' _ hdd]
    calc ‖y‖ = √(‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
      _ ≤ √(ε * dd) := Real.sqrt_le_sqrt hy
  have hxy : ‖x + y‖ ≤ (√(1 + η + ε) + √ε) * √dd := by
    calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
      _ ≤ √(1 + η + ε) * √dd + √ε * √dd := add_le_add hx' hy'
      _ = (√(1 + η + ε) + √ε) * √dd := by ring
  calc ‖x + y‖ ^ 2 ≤ ((√(1 + η + ε) + √ε) * √dd) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
    _ = (√(1 + η + ε) + √ε) ^ 2 * dd := by rw [mul_pow, Real.sq_sqrt hdd]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
