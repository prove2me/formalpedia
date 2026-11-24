-- Prove2me | solution 1 for Formalism.GM.FockB.biHom_of_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:41.665182+00:00
-- url     : https://prove2.me/submissions/88d86ac6-f52f-46df-bb5b-fd45eae577e8

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_ld_biHom_of_euler


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
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.FockB
theorem _root_.solution [CharZero k] {o n : ℕ} {y : MvPolynomial σ k} (h : Good w e zv sv o n y) :
    BiHom w e o n y :=
  Formalism.GM.ld_biHom_of_euler (by rw [← ProjS.eulL_apply]; exact h.1) (by rw [← ProjS.eulL_apply]; exact h.2.1)
end Formalism.GM.FockB
