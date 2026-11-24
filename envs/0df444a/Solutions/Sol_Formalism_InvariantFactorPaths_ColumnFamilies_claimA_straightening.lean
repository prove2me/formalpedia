-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.claimA_straightening
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:47.682807+00:00
-- url     : https://prove2.me/submissions/937ece71-b1b7-4f76-9b74-b77621046665

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LemmaA
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_linearIndependent_standard_tableauBideterminant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Phi_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_mapCoord_brk


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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA := by
  intro n _ mu _ F _
  have hu : IsUnit (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) :=
    (Units.isUnit _).map _
  have h := (linearIndependent_standard_tableauBideterminant F mu).map' (qa_Phi F n _) (LinearMap.ker_eq_bot.mpr (qa_Phi_inj F n _ hu))
  have he : (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1)) =
      (qa_Phi F n (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n))) ∘
        fun I : {I : TIdx mu // StdT I} => qa_P F I.1 := by
    funext I
    exact qa_mapCoord_brk mu F I.1
  rw [he]
  exact h
end Formalism.InvariantFactorPaths.ColumnFamilies
