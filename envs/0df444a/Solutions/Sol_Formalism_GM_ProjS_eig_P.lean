-- Prove2me | solution 1 for Formalism.GM.ProjS.eig_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:14.895487+00:00
-- url     : https://prove2.me/submissions/153ad0dd-d623-4756-805f-cf46d7bf57be

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_tieE_pow
import Theorems.Thm_Formalism_GM_ProjS_tv_w
import Theorems.Thm_Formalism_GM_ProjS_tv_e
import Theorems.Thm_Formalism_GM_ProjS_tv_we
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
theorem _root_.solution (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) (c : ℕ → k) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ)
      (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) =
      ((o + z : ℕ) : k) • (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ)
      (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) =
      (n : k) • (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) := by
  have hw' := tv_w hv
  have he' := tv_e hv
  have hd := tv_we hv
  constructor
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have h1 := eig_v (z := z) hv hy hz l
    have h2 := (eulL_tieE_pow hw' he' hd _ _ _ h1.1 h1.2.1 l).1
    rw [map_smul, h2, sub_add_cancel, smul_comm]
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have h1 := eig_v (z := z) hv hy hz l
    have h2 := (eulL_tieE_pow hw' he' hd _ _ _ h1.1 h1.2.1 l).2
    rw [map_smul, h2, sub_add_cancel, smul_comm]
end Formalism.GM.ProjS
