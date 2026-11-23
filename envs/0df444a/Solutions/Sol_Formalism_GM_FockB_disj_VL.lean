-- Prove2me | solution 1 for Formalism.GM.FockB.disj_VL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:59.52072+00:00
-- url     : https://prove2.me/submissions/7b74ac48-a680-43c4-b75d-42b23246f0e9

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ α : Type} [Field k] {r : ℕ} (w e : α → Fin r → σ) (zv sv : α → σ) (z : α → ℕ)
variable {w e zv sv z}
namespace Formalism.GM.FockB
theorem _root_.solution {a : α} {L : List α} (h : ∀ b ∈ L, Disjoint (Va w e zv sv a) (Va w e zv sv b)) :
    Disjoint (Va w e zv sv a) (VL w e zv sv L) :=
  Set.disjoint_left.mpr fun _ hv ⟨b, hb, hvb⟩ => Set.disjoint_left.mp (h b hb) hv hvb
end Formalism.GM.FockB
