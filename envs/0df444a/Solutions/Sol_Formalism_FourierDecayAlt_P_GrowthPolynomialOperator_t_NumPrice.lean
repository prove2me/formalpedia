-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_NumPrice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.031836+00:00
-- url     : https://prove2.me/submissions/16e15618-125b-4e51-90ee-3fe0ba39558b

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_price_exponential_bound

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
theorem _root_.solution : NumPrice := by
  intro f k b g1 g2 hb hk hf h1 h2
  obtain ⟨-, a1, b1, c1⟩ := price_exponential_bound f k b g1 hb hk hf h1
  obtain ⟨-, a2, b2, c2⟩ := price_exponential_bound f k b g2 hb hk hf h2
  refine ⟨a1, a2, mul_nonneg b1 b2, ?_⟩
  calc (1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f
      ≤ Real.exp (3 * (b ^ 7)⁻¹) * Real.exp (3 * (b ^ 7)⁻¹) :=
        mul_le_mul c1 c2 b2 (Real.exp_pos _).le
    _ = Real.exp (6 * (b ^ 7)⁻¹) := by
        rw [← Real.exp_add]
        congr 1
        ring
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
