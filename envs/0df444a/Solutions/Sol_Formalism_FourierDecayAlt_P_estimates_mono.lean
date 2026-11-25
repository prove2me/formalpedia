-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.estimates_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:07.026324+00:00
-- url     : https://prove2.me/submissions/fe9283b8-8e2c-4089-a3c8-4aa3a16cfda8

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_maj_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_baseGram_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_Nst_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_blk_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.EstimatesMono := by
  intro E W _ D szD' szL' vol' C₄ hC4 hav hD hL hV hG hW
  refine ⟨?_, ?_, ?_⟩
  · intro h ε hε i hi1 hi2 w hw hcnt
    obtain ⟨θ, hθ, H⟩ := h ε hε i hi1 hi2 w hw hcnt
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ
    obtain ⟨e0, el⟩ := H Y hY κ hκ
    refine ⟨e0, fun l hl hl0 => ?_⟩
    obtain ⟨A, hA⟩ := el l hl hl0
    refine ⟨A, le_trans hA ?_⟩
    exact mul_le_mul_of_nonneg_right
      (maj_mono D (D.szD i) (szD' i) l (fun v => hD i v) (fun v => hav v l))
      (Finset.sum_nonneg fun w' _ => mul_nonneg ((hθ A).1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))
  · intro h ε hε i s hs hsi hi hns w hw hcnt
    obtain ⟨θ, hθ, H⟩ := h ε hε i s hs hsi hi hns w hw hcnt
    refine ⟨θ, hθ, ?_⟩
    intro Y S κ hY hκ t ht t' ht' h0 h0' hne
    obtain ⟨π, hπ⟩ := H Y S κ hY hκ t ht t' ht' h0 h0' hne
    refine ⟨π, le_trans hπ ?_⟩
    exact mul_le_mul_of_nonneg_right
      (maj_mono D (D.szL (i - s + 1) s) (szL' (i - s + 1) s) _ (fun v => hL _ _ v)
        (fun v => hav v _))
      (Finset.sum_nonneg fun x _ => mul_nonneg ((hθ π).1 x) (div_nonneg (add_nonneg
        (Nst_nonneg D hG hW hε i s x.1 Y (blk_psd hκ ht) t)
        (Nst_nonneg D hG hW hε i s x.2 Y (blk_psd hκ ht') t')) (by norm_num)))
  · intro h ε hε i s hs hsi hi w hw hcnt hvol
    obtain ⟨θ, hθ, H⟩ := h ε hε i s hs hsi hi w hw hcnt (le_trans (hV _ _).2 hvol)
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ t₀ S hS
    refine le_trans (H Y hY κ hκ t₀ S hS) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun s' _ => (hV _ s').1) (fun s' _ => (hV _ s').2)) (pow_nonneg hC4 _))
      (Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))
end Formalism.FourierDecayAlt.P
