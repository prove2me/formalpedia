-- Prove2me | solution 1 for D1Bound5.bennett_sum_divisible_in_subring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:28:06.375055+00:00
-- url     : https://prove2.me/submissions/2fc36724-066f-46d6-9537-9e4b7046abd2

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

section
open Finset

namespace D1Bound5

/-- A finite sum of multiples whose quotients lie in a fixed subring has a
quotient in that same subring. The divisor itself need not belong to it. -/
theorem _root_.solution
    {F T : Type*} [CommRing F] (S : Subring F) (s : Finset T)
    (x : T → F) (d : F)
    (h : ∀ t ∈ s, ∃ q ∈ S, x t = d * q) :
    ∃ q ∈ S, ∑ t ∈ s, x t = d * q := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      exact ⟨0, S.zero_mem, by simp⟩
  | @insert t s hts ih =>
      intro h
      obtain ⟨q, hq, hx⟩ := h t (Finset.mem_insert_self t s)
      obtain ⟨r, hr, hs⟩ := ih (fun u hu ↦ h u (Finset.mem_insert_of_mem hu))
      refine ⟨q + r, S.add_mem hq hr, ?_⟩
      rw [Finset.sum_insert hts, hx, hs, mul_add]



end D1Bound5
end
