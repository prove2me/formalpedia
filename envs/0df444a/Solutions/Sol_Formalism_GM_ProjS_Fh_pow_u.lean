-- Prove2me | solution 1 for Formalism.GM.ProjS.Fh_pow_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:38.849435+00:00
-- url     : https://prove2.me/submissions/2dabcf00-6275-4fe2-9299-8be7d87d51bd

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_Fh_v

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
theorem _root_.solution (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) (l : ℕ) :
    (tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l) (X zv ^ z * y) =
      (tieF w e ^ l) (X zv ^ z * y) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ' (Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)) l, Module.End.mul_apply, ih,
      Fh_v hv hz l]
end Formalism.GM.ProjS
