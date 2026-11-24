-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_emb_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:27.93283+00:00
-- url     : https://prove2.me/submissions/6e39054f-3447-45c3-a1d8-e60a3f5fb28e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite

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
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {k : ℕ} (h : S.card = k) (h' : (S.map Fin.castSuccEmb).card = k) :
    ⇑((S.map Fin.castSuccEmb).orderEmbOfFin h') = fun a => (S.orderEmbOfFin h a).castSucc := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a; simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono hab)
end Formalism.InvariantFactorPaths.ColumnFamilies
