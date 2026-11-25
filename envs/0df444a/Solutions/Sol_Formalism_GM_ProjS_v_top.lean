-- Prove2me | solution 1 for Formalism.GM.ProjS.v_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:15.995805+00:00
-- url     : https://prove2.me/submissions/3e4553d8-7730-4b18-83c3-831aa5dde8f7

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eq_zero_of_eulL
import Theorems.Thm_Formalism_GM_ProjS_eig_v

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
variable {o n z : ℕ} {y : MvPolynomial σ k}
namespace Formalism.GM.ProjS
theorem _root_.solution [CharZero k] (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    (tieF w e ^ (o + 1)) (X zv ^ z * y) = 0 :=
  eq_zero_of_eulL w o (o + 1) (Nat.lt_succ_self o) _
    (eig_v (z := z) hv hy hz (o + 1)).2.2
end Formalism.GM.ProjS
