-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.corollary_product_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:58:20.580094+00:00
-- url     : https://prove2.me/submissions/b7d9d081-600f-4828-9c08-1eb161624b02

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_holder_lintegral_prod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentProductBound := by
  intro Ω _ μ _ r q L l H1 hm hpos hH1 hL h
  have hcard : (univ.filter (fun a : Fin (r + 1) => a.val < L)).card = L := by
    have := Fin.card_filter_val_lt (n := r + 1) (m := L)
    simpa [hL] using this
  have e : ∀ ω, ENNReal.ofReal ((∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), l a ω) ^ (2 * q)) =
      ∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), ENNReal.ofReal (l a ω ^ (2 * q)) := by
    intro ω
    rw [← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg]
    intro i _
    have := hpos i ω
    positivity
  simp_rw [e]
  have key := holder_lintegral_prod_le μ (univ.filter (fun a : Fin (r + 1) => a.val < L))
    (fun a ω => ENNReal.ofReal (l a ω ^ (2 * q))) (fun _ => ENNReal.ofReal (H1 ^ (2 * q)))
    (fun a _ => ENNReal.measurable_ofReal.comp ((hm a).pow_const _))
    (by
      intro a ha
      rw [hcard]
      have h3 := h a (by simpa using ha)
      rw [← ENNReal.ofReal_pow (by positivity), ← pow_mul]
      refine le_trans (le_of_eq ?_) h3
      refine lintegral_congr fun ω => ?_
      have := hpos a ω
      rw [← ENNReal.ofReal_pow (by positivity), ← pow_mul])
  refine key.trans (le_of_eq ?_)
  rw [prod_const, hcard, ← ENNReal.ofReal_pow (by positivity), ← pow_mul]
end Formalism.HermitianLatticeCounting.P
