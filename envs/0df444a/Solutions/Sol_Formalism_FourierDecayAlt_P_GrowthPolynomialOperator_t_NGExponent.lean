-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_NGExponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.201615+00:00
-- url     : https://prove2.me/submissions/15dd18af-71d5-4a66-8b29-6cb550557dab

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_inv_two_pow

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
theorem _root_.solution : NGExponent := by
  intro k r h
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * r + 5 + j := ⟨k - (2 * r + 5), by omega⟩
  have hj : 2 * r + 5 + j - 2 * r - 5 = j := by omega
  rw [hj, inv_two_pow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h2 : ((4 * r + 10 : ℕ) : ℝ) ≤ ((2 * r + 5 + j : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h2 ⊢
  linarith
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
