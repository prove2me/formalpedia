-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_key_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:44.704498+00:00
-- url     : https://prove2.me/submissions/257bf19c-b757-44c3-85a0-8df3d6fadf2a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (j : CF.J) (I : TIdx (CF.mu j)) (i : M.ι) :
    qb_ev M F (CF.mu j) (fun i => (CF.vec j I i : F)) i =
      (CF.ph j i (canT (CF.mu j)) : GLCoord F n) * mapCoord F (brk (CF.mu j) I) := by
  rw [qb_key]
  simp only [qb_wtT_eq_iff (CF.dom j), sum_ite_eq', mem_univ, if_true, brk]
end Formalism.InvariantFactorPaths.ColumnFamilies
