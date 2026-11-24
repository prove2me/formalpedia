-- Prove2me | solution 1 for Formalism.GM.ProjS.mix_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:10.733837+00:00
-- url     : https://prove2.me/submissions/58aa03d0-2e55-4de4-9cd6-f07824eae3ae

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, w d = w c) ∧ ∀ d, w d ≠ e c) ∨ ((∀ d, w d ≠ w c) ∧ ∃ d, w d = e c) := fun c => Or.inl ⟨⟨c, rfl⟩, fun d => hv.2.2.1 d c⟩
end Formalism.GM.ProjS
