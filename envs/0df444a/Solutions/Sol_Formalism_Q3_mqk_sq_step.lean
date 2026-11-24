-- Prove2me | solution 1 for Formalism.Q3.mqk_sq_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:02.512439+00:00
-- url     : https://prove2.me/submissions/92f8a7a2-74c4-4c3c-809a-88ee6b413083

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
import Theorems.Thm_Formalism_Q3_mqk_mem_adjoin_form

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
theorem _root_.solution [CharZero E] (K : IntermediateField F E) (β b d : E) (hb : b ∈ K) (hd : d ∈ K)
    (hβ : β ^ 2 = b) (hβK : β ∉ K) {y : E} (hy : y ∈ IntermediateField.adjoin K {β})
    (hyd : y ^ 2 = d) :
    (∃ z ∈ K, z ^ 2 = d) ∨ (∃ z ∈ K, z ^ 2 = d * b) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mqk_mem_adjoin_form K β b hb hβ hy
  have key : (u + v * β) ^ 2 = u ^ 2 + v ^ 2 * b + 2 * u * v * β := by rw [← hβ]; ring
  by_cases huv : u * v = 0
  · rcases mul_eq_zero.1 huv with h | h
    · right
      refine ⟨v * b, K.mul_mem hv hb, ?_⟩
      rw [← hyd, h, ← hβ]
      ring
    · left
      refine ⟨u, hu, ?_⟩
      rw [← hyd, h]
      ring
  · exfalso
    apply hβK
    have h2 : (2 : E) * u * v ≠ 0 := by
      rw [mul_assoc]
      exact mul_ne_zero two_ne_zero huv
    have hβeq : β = (d - u ^ 2 - v ^ 2 * b) / (2 * u * v) := by
      rw [eq_div_iff h2, ← hyd, key]
      ring
    have h2K : (2 : E) ∈ K := by
      have := K.add_mem K.one_mem K.one_mem
      rw [one_add_one_eq_two] at this
      exact this
    rw [hβeq]
    exact K.div_mem (K.sub_mem (K.sub_mem hd (_root_.pow_mem hu 2)) (K.mul_mem (_root_.pow_mem hv 2) hb))
      (K.mul_mem (K.mul_mem h2K hu) hv)
end Formalism.Q3
