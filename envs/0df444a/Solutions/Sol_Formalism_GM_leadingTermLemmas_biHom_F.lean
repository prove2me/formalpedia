-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:39.754402+00:00
-- url     : https://prove2.me/submissions/21c802de-4f4b-411b-9c0e-a64e31e1f259

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sum
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_pderiv_w
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_pderiv_e
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
variable (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {a b : ℕ} {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e (a - 1) (b - 1) (tieF w e u) ∧ (a = 0 ∨ b = 0 → tieF w e u = 0) := by
  rw [tieF_apply']
  refine ⟨biHom_sum _ _ (fun c _ => ?_), fun h => Finset.sum_eq_zero (fun c _ => ?_)⟩
  · exact (biHom_pderiv_w hw he hwe c (biHom_pderiv_e hw he hwe c hu).1).1
  · rcases h with h | h
    · exact (biHom_pderiv_w hw he hwe c (biHom_pderiv_e hw he hwe c hu).1).2 h
    · rw [(biHom_pderiv_e hw he hwe c hu).2 h, map_zero]
end Formalism.GM.leadingTermLemmas
