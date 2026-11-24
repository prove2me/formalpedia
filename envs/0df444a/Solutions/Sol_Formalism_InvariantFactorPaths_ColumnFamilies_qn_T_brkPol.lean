-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_brkPol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:31.376797+00:00
-- url     : https://prove2.me/submissions/f6034205-8812-4127-b077-d4ce2d23618d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_det
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_brkPol_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_transposeVariables_involutive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) = qn_delta n ^ (mu (lastIdx n)).toNat * qa_P ℤ I := by
  rw [qa_brkPol_eq, map_mul, map_pow, qn_T_det]
  congr 1
  exact transposeVariables_involutive ℤ n (qa_P ℤ I)
end Formalism.InvariantFactorPaths.ColumnFamilies
