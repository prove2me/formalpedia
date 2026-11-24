-- Prove2me | solution 1 for FairChores.MMS_mem_chores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:07.432264+00:00
-- url     : https://prove2.me/submissions/d4719e08-cfc7-46e9-aa30-2f658fa5dfb0

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_mem_MMSset_iff
import Theorems.Thm_FairChores_exists_min_outcome
import Theorems.Thm_FairChores_MMSset_bddBelow


set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (hn : 0 < n) (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) :
    MMS n c p ∈ MMSset n c p := by
  obtain ⟨o, hovalid, homin⟩ := exists_min_outcome c p hp hn
  have hlb : ∀ r ∈ MMSset n c p, maxCost c o ≤ r := by
    intro r hr
    obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn c p r).mp hr
    exact (homin o' hv').trans hr'
  have hmem : maxCost c o ∈ MMSset n c p := (mem_MMSset_iff hn c p _).mpr ⟨o, hovalid, le_rfl⟩
  have hEq : MMS n c p = maxCost c o :=
    le_antisymm (csInf_le (MMSset_bddBelow hc hn) hmem) (le_csInf ⟨_, hmem⟩ hlb)
  rw [hEq]; exact hmem
end FairChores
