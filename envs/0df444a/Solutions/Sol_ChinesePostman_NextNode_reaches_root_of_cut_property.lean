-- Prove2me | solution 1 for ChinesePostman.NextNode.reaches_root_of_cut_property
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:35:48.729959+00:00
-- url     : https://prove2.me/submissions/65567265-19ff-46a8-8819-140133749f03

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting



namespace ChinesePostman.NextNode

theorem reaches_root_core {V : Type} [Fintype V] [DecidableEq V] (p : V → V) (r : V)
    (h : ∀ S : Finset V, S.Nonempty → r ∉ S → ∃ n ∈ S, p n ∉ S) :
    ∀ n, ∃ j : ℕ, (fun u => if u = r then r else p u)^[j] n = r := by
  classical
  by_contra hc
  push_neg at hc
  obtain ⟨n0, hn0⟩ := hc
  let S : Finset V := Finset.univ.filter (fun n => ∀ j : ℕ, (fun u => if u = r then r else p u)^[j] n ≠ r)
  have hne : S.Nonempty := ⟨n0, by simp [S, hn0]⟩
  have hr : r ∉ S := by
    intro hr
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact hr 0 rfl
  obtain ⟨n, hnS, hpn⟩ := h S hne hr
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hnS hpn
  obtain ⟨j, hj⟩ := hpn
  have hnr : n ≠ r := by
    intro e; subst e; exact hnS 0 rfl
  apply hnS (j+1)
  rw [Function.iterate_succ_apply]
  simpa [hnr] using hj

end ChinesePostman.NextNode

open ChinesePostman.NextNode


theorem solution {V : Type} [Fintype V] [DecidableEq V] (p : V → V) (r : V)
    (h : ∀ S : Finset V, S.Nonempty → r ∉ S → ∃ n ∈ S, p n ∉ S) :
    ∀ n, ∃ j : ℕ, (fun u => if u = r then r else p u)^[j] n = r := by
  exact reaches_root_core p r h
