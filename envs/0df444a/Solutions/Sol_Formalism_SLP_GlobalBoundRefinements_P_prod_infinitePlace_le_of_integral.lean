-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.prod_infinitePlace_le_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:18.127088+00:00
-- url     : https://prove2.me/submissions/0ec89199-0d36-46b7-b4b7-aa73bdbdd352

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ProdInfinitePlaceLeOfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.ThmBNorm := by
  intro F _ _ s q x hs hq hβ hw
  obtain ⟨β, hβ⟩ := hβ
  have hβ0 : β ≠ 0 := by
    intro h0
    have : s / q = 0 := by rw [← hβ, h0]; simp
    exact div_ne_zero hs hq this

  have hN : (1 : ℝ) ≤ ∏ w : NumberField.InfinitePlace F, w (s / q) ^ w.mult := by
    rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← hβ, ← Algebra.coe_norm_int]
    have hne : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ0
    have : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hne
    exact_mod_cast this
  have hdiv : ∏ w : NumberField.InfinitePlace F, w (s / q) ^ w.mult =
      (∏ w : NumberField.InfinitePlace F, w s ^ w.mult) / ∏ w : NumberField.InfinitePlace F, w q ^ w.mult := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [map_div₀, div_pow]
  have hqpos : 0 < ∏ w : NumberField.InfinitePlace F, w q ^ w.mult :=
    Finset.prod_pos (fun w _ => pow_pos (NumberField.InfinitePlace.pos_iff.mpr hq) _)
  have hsle : ∏ w : NumberField.InfinitePlace F, w s ^ w.mult ≤ ∏ w, (x w ^ 2) ^ w.mult :=
    Finset.prod_le_prod (fun w _ => pow_nonneg (NumberField.InfinitePlace.pos_iff.mpr hs).le _)
      (fun w _ => pow_le_pow_left₀ (NumberField.InfinitePlace.pos_iff.mpr hs).le (hw w) _)
  rw [hdiv, le_div_iff₀ hqpos, one_mul] at hN
  linarith
end Formalism.SLP.GlobalBoundRefinements.P
