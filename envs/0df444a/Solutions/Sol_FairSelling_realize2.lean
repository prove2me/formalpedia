-- Prove2me | solution 1 for FairSelling.realize2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:09.301578+00:00
-- url     : https://prove2.me/submissions/8dadac78-67d4-4ab1-a759-6427ef8b1131

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin 2 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (B0 B1 F : Finset G) (r0 r1 : ℝ)
    (hd01 : Disjoint B0 B1) (hdF0 : Disjoint F B0) (hdF1 : Disjoint F B1)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hsum : r0 + r1 ≤ ∑ g ∈ F, p g) :
    ∃ o : Outcome G 2, o.Valid p ∧
      util (v 0) o 0 = vbarSum (v 0) p B0 + r0 ∧
      util (v 1) o 1 = vbarSum (v 1) p B1 + r1 := by
  refine ⟨unifiedOutcome v p ![B0, B1] F ![r0, r1], ?_, ?_, ?_⟩
  · apply unifiedOutcome_valid v p hp
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [hd01.symm]
    · intro i; fin_cases i <;> simpa using ‹_›
    · intro i; fin_cases i <;> simpa
    · rw [Fin.sum_univ_two]; simpa using hsum
  · rw [util_unifiedOutcome]; simp
  · rw [util_unifiedOutcome]; simp
end FairSelling
