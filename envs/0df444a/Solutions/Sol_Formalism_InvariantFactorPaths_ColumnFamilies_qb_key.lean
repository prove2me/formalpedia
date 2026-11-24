-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:22:09.182896+00:00
-- url     : https://prove2.me/submissions/03a9b8ee-0ec1-4101-95fe-e6aab8b97da9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_keyZ

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
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (j : CF.J) (I : TIdx (CF.mu j))
    (nu : Fin n → ℤ) (i : M.ι) :
    qb_ev M F nu (fun i => (CF.vec j I i : F)) i =
      ∑ K, if qb_wtT (CF.mu j) K = nu then (CF.ph j i K : GLCoord F n) * mapCoord F (TMat (CF.mu j) K I)
        else 0 := by
  have h := congrArg (mapCoord F) (qb_keyZ CF j I nu i)
  simp only [map_sum, map_mul, map_intCast, apply_ite (mapCoord F), map_zero] at h
  rw [← h, qb_ev_apply]
  simp only [ColFam.vec, map_intCast]
end Formalism.InvariantFactorPaths.ColumnFamilies
