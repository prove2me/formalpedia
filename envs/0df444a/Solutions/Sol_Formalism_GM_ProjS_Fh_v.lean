-- Prove2me | solution 1 for Formalism.GM.ProjS.Fh_v
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:37.862232+00:00
-- url     : https://prove2.me/submissions/b0ee7596-422c-4337-9b6c-4616b82c014a

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_tieF_pow_pderiv
import Theorems.Thm_Formalism_GM_ProjS_tieFh_eq
import Theorems.Thm_Formalism_GM_ProjS_pderiv_sv_u

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
    tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ((tieF w e ^ l) (X zv ^ z * y)) =
      (tieF w e ^ (l + 1)) (X zv ^ z * y) := by
  have hsplit : ∀ g : MvPolynomial σ k, Formalism.GM.tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) g =
      pderiv zv (pderiv sv g) + Formalism.GM.tieF w e g := by
    intro g
    rw [← tieFh_eq]
    rfl
  rw [hsplit, ← tieF_pow_pderiv, pderiv_sv_u hv hz, map_zero, map_zero, zero_add,
    pow_succ' (Formalism.GM.tieF w e) l, Module.End.mul_apply]
end Formalism.GM.ProjS
