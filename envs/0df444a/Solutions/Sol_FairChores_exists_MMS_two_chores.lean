-- Prove2me | solution 1 for FairChores.exists_MMS_two_chores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:04:08.373972+00:00
-- url     : https://prove2.me/submissions/25461fbc-a15c-4ae6-a8d2-1c50d085930d

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_exists_reducedC
import Theorems.Thm_FairChores_configC_sum_bound
import Theorems.Thm_FairChores_cost_swapOutcomeC
import Theorems.Thm_FairChores_swapOutcomeC_valid
import Theorems.Thm_FairChores_cutgiveC
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c : Fin 2 → T → ℝ) (p : T → ℝ)
    (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T 2, o.Valid p ∧ ∀ i, cost (c i) o i ≤ MMS 2 (c i) p := by
  obtain ⟨Ac0, sc0, qc0, hcfg0, hcard0⟩ := exists_reducedC (c 0) p (hc 0) hp
  obtain ⟨Ac1, sc1, qc1, hcfg1, hcard1⟩ := exists_reducedC (c 1) p (hc 1) hp
  have hb0 := configC_sum_bound (c 0) p (MMS 2 (c 0) p) Ac0 sc0 qc0 hcfg0
  have hb1 := configC_sum_bound (c 1) p (MMS 2 (c 1) p) Ac1 sc1 qc1 hcfg1
  by_cases hcut : ∑ t ∈ sc0, p t ≤ ∑ t ∈ sc1, p t
  · obtain ⟨o, hov, h0, h1⟩ := cutgiveC c p hp Ac0 sc0 qc0 hcfg0 sc1 hcard1 hb1 hcut
    exact ⟨o, hov, fun i => by fin_cases i <;> assumption⟩
  · push_neg at hcut
    obtain ⟨o, hov, h0, h1⟩ := cutgiveC (fun i => c (Equiv.swap 0 1 i)) p hp Ac1 sc1 qc1
      (by simpa [Equiv.swap_apply_left] using hcfg1) sc0 hcard0
      (by simpa [Equiv.swap_apply_right] using hb0) (le_of_lt hcut)
    refine ⟨swapOutcomeC o, swapOutcomeC_valid p o hov, fun i => ?_⟩
    fin_cases i
    · rw [cost_swapOutcomeC]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h1
    · rw [cost_swapOutcomeC]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h0
end FairChores
