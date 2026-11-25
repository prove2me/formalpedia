-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.pigeon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:17:04.384977+00:00
-- url     : https://prove2.me/submissions/ded4d6c4-3cd1-4338-a736-33fd506b7387

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_q_two_le
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_root_bound
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_norm_maps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (hq : Fintype.card L = q ^ 2) :
    (Sfix L q).card = q - 1 ∧ ∀ d ∈ Sfix L q, (fib q d).card = q + 1 := by
  have h2 := q_two_le hq
  have htot := card_eq_sum_card_fiberwise (norm_maps hq)
  rw [card_erase_of_mem (mem_univ _), card_univ, hq] at htot
  have hfib : ∀ d ∈ Sfix L q, (fib q d).card ≤ q + 1 := by
    intro d _
    calc (fib q d).card ≤ (univ.filter (fun x : L => x ^ (q + 1) = d)).card := by
          apply card_le_card
          intro x
          simp only [fib, mem_filter, mem_erase, mem_univ, and_true, true_and]
          exact fun h => h.2
      _ ≤ q + 1 := root_bound _ (by omega) d
  have hS : (Sfix L q).card ≤ q - 1 := by
    calc _ ≤ (univ.filter (fun x : L => x ^ (q - 1) = 1)).card := by
          apply card_le_card
          intro c hc
          simp only [Sfix, mem_filter, mem_univ, true_and] at hc ⊢
          obtain ⟨h0, h1⟩ := hc
          have : c ^ (q - 1) * c = 1 * c := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
          exact mul_right_cancel₀ h0 this
      _ ≤ q - 1 := root_bound _ (by omega) 1
  have hle : ∑ d ∈ Sfix L q, (fib q d).card ≤ ∑ d ∈ Sfix L q, (q + 1) := sum_le_sum hfib
  rw [sum_const, smul_eq_mul] at hle
  have htot' : q ^ 2 - 1 = ∑ d ∈ Sfix L q, (fib q d).card := htot
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hsq : (r + 2) ^ 2 - 1 = (r + 1) * (r + 3) := by
    have : (r + 2) ^ 2 = (r + 1) * (r + 3) + 1 := by ring
    omega
  have hS' : (Sfix L (r + 2)).card = r + 1 := by
    have h3 : (r + 1) * (r + 3) ≤ (Sfix L (r + 2)).card * (r + 3) := by
      rw [← hsq, htot']; exact hle
    have h4 : (Sfix L (r + 2)).card ≤ r + 1 := by simpa using hS
    have h5 := Nat.le_of_mul_le_mul_right h3 (by omega)
    omega
  refine ⟨by simpa using hS', ?_⟩
  have heq : ∑ d ∈ Sfix L (r + 2), (fib (r + 2) d).card = ∑ d ∈ Sfix L (r + 2), (r + 2 + 1) := by
    rw [← htot', hsq, sum_const, smul_eq_mul, hS']
  exact (sum_eq_sum_iff_of_le hfib).1 heq
end Formalism.LogVandermondeBounds.StandardLattice
