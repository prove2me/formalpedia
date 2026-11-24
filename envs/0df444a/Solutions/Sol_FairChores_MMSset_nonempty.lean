-- Prove2me | solution 1 for FairChores.MMSset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:19.66822+00:00
-- url     : https://prove2.me/submissions/c1c17ed1-ded1-43f7-8fd0-0d4cdd1b32f2

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : (MMSset n c p).Nonempty := by
  classical
  refine ⟨∑ t, c t, ⟨∅, fun j => if j = ⟨0, hn⟩ then Finset.univ else ∅, fun _ => 0⟩, ?_, ?_⟩
  · refine ⟨by simp, ?_, ?_, by simp, by simp⟩
    · intro j k hjk
      by_cases hj : j = ⟨0, hn⟩ <;> by_cases hk : k = ⟨0, hn⟩ <;> simp [hj, hk]
      exact absurd (hj.trans hk.symm) hjk
    · refine Finset.eq_univ_iff_forall.mpr fun t => ?_
      simp only [Finset.empty_union, Finset.mem_biUnion]
      exact ⟨⟨0, hn⟩, Finset.mem_univ _, by simp⟩
  · intro j
    by_cases hj : j = ⟨0, hn⟩
    · simp [cost, hj]
    · simp [cost, hj]
      exact Finset.sum_nonneg fun t _ => hc t
end FairChores
