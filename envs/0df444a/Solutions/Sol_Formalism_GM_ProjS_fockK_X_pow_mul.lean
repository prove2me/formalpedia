-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:08.289875+00:00
-- url     : https://prove2.me/submissions/c0b16e13-3bbb-4ae0-a3e3-9b7282c27323

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_X_mul

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
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution (v : σ) (z : ℕ) (a h : MvPolynomial σ k) :
    M.fockK (X v ^ z * a) h = M.fockK a (((pderiv v).toLinearMap ^ z) h) := by
  induction z generalizing h with
  | zero => simp
  | succ z ih =>
    rw [pow_succ' (X v : MvPolynomial σ k) z, mul_assoc, fockK_X_mul, ih, pow_succ, Module.End.mul_apply]
    try rfl
end Formalism.GM.ProjS
