-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_can_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:52.926423+00:00
-- url     : https://prove2.me/submissions/829ddafd-4408-431b-8002-27623e6cf1c5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2
    (f := fun a : Fin (colH mu c) => Fin.castLE (colH_le mu c) a) (by intro x; simp [canT])
    (Fin.strictMono_castLE _)
  exact (congrFun this a).symm
end Formalism.InvariantFactorPaths.ColumnFamilies
