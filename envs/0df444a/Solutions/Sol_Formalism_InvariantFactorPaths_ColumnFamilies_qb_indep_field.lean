-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_indep_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:48.196369+00:00
-- url     : https://prove2.me/submissions/215bd563-f4e2-4f12-9104-8e25480ce9ab

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_supp_in

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
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] :
    LinearIndependent F (qb_vecF CF F) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha x
  by_contra hx
  refine qb_supp_in hA CF F a ∅ ⟨fun _ h => h.elim, fun _ h => h.elim⟩ (fun mu _ _ => ?_) x hx
  rw [ha, ← qb_evL_apply, map_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
