-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.rowShift_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:52.971641+00:00
-- url     : https://prove2.me/submissions/01f5032b-5991-4398-b59f-dc9433c880eb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ)
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (σ0 : Ty) (i i' : Fin (r σ0)) (t : k)
    (p : MvPolynomial (Letter Ty r n) k) :
    rowShift r n k' σ0 i i' (φ t) (map φ p) = map φ (rowShift r n k σ0 i i' t p) := by
  simp only [rowShift, aeval_def, algebraMap_eq, map_eval₂]
  congr 1
  funext ℓ
  simp only [Function.comp_apply]
  split_ifs <;> simp
end Formalism.L2.FormalSeriesBounds.HaP
