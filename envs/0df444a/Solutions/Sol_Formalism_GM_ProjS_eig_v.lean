-- Prove2me | solution 1 for Formalism.GM.ProjS.eig_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:18.544477+00:00
-- url     : https://prove2.me/submissions/83ef90bf-c8a1-4425-a8af-a7798a46c842

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_tieF_pow
import Theorems.Thm_Formalism_GM_ProjS_tv_w
import Theorems.Thm_Formalism_GM_ProjS_tv_e
import Theorems.Thm_Formalism_GM_ProjS_mix_w
import Theorems.Thm_P2M_Formalism_GM_ProjS_mix_w__f4375b1a0220
import Theorems.Thm_P2M_Formalism_GM_ProjS_mix_e__3cb99070d549
import Theorems.Thm_Formalism_GM_ProjS_eig_u

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
theorem _root_.solution (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) (l : ℕ) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ) ((tieF w e ^ l) (X zv ^ z * y)) =
      (((o + z : ℕ) : k) - l) • (tieF w e ^ l) (X zv ^ z * y) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ) ((tieF w e ^ l) (X zv ^ z * y)) =
      ((n : k) - l) • (tieF w e ^ l) (X zv ^ z * y) ∧
    eulL w ((tieF w e ^ l) (X zv ^ z * y)) = ((o : k) - l) • (tieF w e ^ l) (X zv ^ z * y) := by
  have h0 := eig_u (z := z) hv hy hz
  exact ⟨eulL_tieF_pow _ (tv_w hv) w e (mix_w' hv) _ _ h0.1 l,
    eulL_tieF_pow _ (tv_e hv) w e (mix_e' hv) _ _ h0.2.1 l,
    eulL_tieF_pow _ hv.1 w e (mix_w hv) _ _ h0.2.2 l⟩
end Formalism.GM.ProjS
