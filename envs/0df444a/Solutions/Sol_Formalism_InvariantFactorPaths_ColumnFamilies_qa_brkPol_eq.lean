-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_brkPol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:42:07.180872+00:00
-- url     : https://prove2.me/submissions/1325924f-427e-4b6a-aef4-c1928bfd91cf

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_prod_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brkPol mu I = (genMat ℤ n).det ^ (mu (lastIdx n)).toNat * rename Prod.swap (qa_P ℤ I) := by
  unfold brkPol
  rw [qa_prod_minor]
end Formalism.InvariantFactorPaths.ColumnFamilies
