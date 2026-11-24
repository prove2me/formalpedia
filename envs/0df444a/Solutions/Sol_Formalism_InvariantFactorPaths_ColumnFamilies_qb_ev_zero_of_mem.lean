-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_ev_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:26.590526+00:00
-- url     : https://prove2.me/submissions/c0776895-0f31-4b2a-a735-788a44644063

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key_zero


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
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] {pi : Set (Fin n → ℤ)}
    (hpi : DomLowerSet pi) {j : CF.J} (hj : CF.mu j ∈ pi) (I : TIdx (CF.mu j)) {mu : Fin n → ℤ}
    (hmu : Dominant mu) (hout : mu ∉ pi) : qb_ev M F mu (fun i => (CF.vec j I i : F)) = 0 :=
  qb_key_zero CF F j I mu fun hle => hout (hpi.2 _ hj _ hmu hle)
end Formalism.InvariantFactorPaths.ColumnFamilies
