-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.card_perm_with_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:56.997321+00:00
-- url     : https://prove2.me/submissions/c09573ff-1c91-4a4e-85ef-450407b3a616

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_two_mul_numDerangements_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints
namespace Formalism.CyclotomicNorms.PermutationFixedPoints
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α] (h : 1 ≤ Fintype.card α) :
    (Fintype.card α).factorial ≤
      2 * (univ.filter (fun p : Equiv.Perm α => ∃ x, p x = x)).card := by
  have hD := card_derangements_eq_numDerangements α
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Equiv.Perm α)))
    (fun p => ∃ x, p x = x)
  have hneg : (univ.filter (fun p : Equiv.Perm α => ¬ ∃ x, p x = x)).card =
      Fintype.card (derangements α) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => by
      simp only [not_exists]
      exact Iff.rfl))
  rw [card_univ, Fintype.card_perm, hneg, hD] at hsplit
  have := two_mul_numDerangements_le _ h
  omega
end Formalism.CyclotomicNorms.PermutationFixedPoints
