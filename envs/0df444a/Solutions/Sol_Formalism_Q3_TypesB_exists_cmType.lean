-- Prove2me | solution 1 for Formalism.Q3.TypesB.exists_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:21:58.314987+00:00
-- url     : https://prove2.me/submissions/befdeda6-d5ce-467b-bde0-ba61abc8af7e

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
import Theorems.Thm_P2M_Formalism_Q3_TypesB_cc_mul__4663f8641e52

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.Q3
open Formalism.Q3.TypesB
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}
namespace Formalism.Q3.TypesB
theorem _root_.solution [Fintype G] (hc1 : c ≠ 1) (hc : c * c = 1) :
    ∃ H : Finset G, IsCMTypeG c H ∧ 1 ∈ H := by
  let e := Fintype.equivFin G
  refine ⟨univ.filter (fun g => g = 1 ∨ (g ≠ c ∧ e g < e (c * g))), ?_, by simp⟩
  intro g
  simp only [mem_filter, mem_univ, true_and, cc_mul' hc]
  by_cases h1 : g = 1
  · subst h1
    simp [hc1]
  by_cases h2 : g = c
  · subst h2
    simp [hc, hc1]
  have h3 : c * g ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun x => c * x) h
    simp only [cc_mul' hc, mul_one] at this
    exact this
  have h4 : c * g ≠ c := by
    intro h
    apply h1
    exact mul_left_cancel (h.trans (mul_one c).symm)
  have h5 : e g ≠ e (c * g) := by
    intro h
    have h' : g = c * g := e.injective h
    apply hc1
    have : 1 * g = c * g := by rw [one_mul]; exact h'
    exact (mul_right_cancel this).symm
  simp only [h1, h2, h3, h4, false_or, ne_eq, not_false_eq_true, true_and, not_lt]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h h5⟩
end Formalism.Q3.TypesB
