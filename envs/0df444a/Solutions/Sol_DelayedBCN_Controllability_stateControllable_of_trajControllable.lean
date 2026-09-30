-- Prove2me | solution 1 for DelayedBCN.Controllability.stateControllable_of_trajControllable
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:04:28.978454+00:00
-- url     : https://prove2.me/submissions/5a1f9fd2-40ee-4387-90c9-6953a785ee75

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix


open DelayedBCN.Controllability

theorem solution {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (h : TrajControllable F) : StateControllable F := by
  intro X0
  rw [Set.eq_univ_iff_forall]
  intro xd
  have hmem : (fun _ : Fin μ => xd) ∈ trajReachableSet F X0 := by
    rw [h X0]
    exact Set.mem_univ _
  simp only [trajReachableSet, trajReachableSetAt, Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨k, hk, U, hU⟩ := hmem
  simp only [stateReachableSet, stateReachableSetAt, Set.mem_iUnion, exists_prop]
  exact ⟨k, hk, U, by rw [hU]; rfl⟩

