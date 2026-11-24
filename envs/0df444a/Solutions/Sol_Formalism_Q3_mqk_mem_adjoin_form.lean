-- Prove2me | solution 1 for Formalism.Q3.mqk_mem_adjoin_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:42.336323+00:00
-- url     : https://prove2.me/submissions/e89f81c5-cb5c-48f1-a341-d7e8b6fc4928

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
namespace Formalism.Q3
theorem _root_.solution (K : IntermediateField F E) (β b : E) (hb : b ∈ K) (hβ : β ^ 2 = b)
    {y : E} (hy : y ∈ IntermediateField.adjoin K {β}) :
    ∃ u ∈ K, ∃ v ∈ K, y = u + v * β := by
  have hint : IsIntegral K β := by
    refine ⟨X ^ 2 - C ⟨b, hb⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [hβ]
  have hy' : y ∈ Algebra.adjoin K {β} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  clear hy
  induction hy' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, K.zero_mem, 1, K.one_mem, by simp [hx]⟩
  | algebraMap r =>
    exact ⟨r, r.2, 0, K.zero_mem, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hz
    exact ⟨u + u', K.add_mem hu hu', v + v', K.add_mem hv hv', by ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hz
    refine ⟨u * u' + v * v' * b, K.add_mem (K.mul_mem hu hu') (K.mul_mem (K.mul_mem hv hv') hb),
      u * v' + v * u', K.add_mem (K.mul_mem hu hv') (K.mul_mem hv hu'), ?_⟩
    rw [← hβ]
    ring
end Formalism.Q3
