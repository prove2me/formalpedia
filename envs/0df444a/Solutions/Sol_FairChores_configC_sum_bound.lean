-- Prove2me | solution 1 for FairChores.configC_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:47.811782+00:00
-- url     : https://prove2.me/submissions/3dedff64-1f39-4c40-a9fe-e00d7d1669b5

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_cbarSum_union
import Theorems.Thm_FairChores_biU_twoC
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) (M : ℝ) (A : Fin 2 → Finset T) (s : Finset T)
    (q : Fin 2 → ℝ) (h : ConfigC c p M A s q) :
    cbarSum c p (Finset.univ \ s) + ∑ t ∈ s, p t ≤ 2 * M := by
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hle⟩ := h
  rw [biU_twoC A] at hcover
  have hAunion : A 0 ∪ A 1 = Finset.univ \ s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (hx | hx)
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 0) hxs hx
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 1) hxs hx
    · intro hxs
      have hmem : x ∈ s ∪ (A 0 ∪ A 1) := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hmem with h' | h'
      · exact absurd h' hxs
      · exact Finset.mem_union.mp h'
  have hcb : cbarSum c p (A 0 ∪ A 1) = cbarSum c p (A 0) + cbarSum c p (A 1) :=
    cbarSum_union c p (hdisjA 0 1 (by decide))
  have hqsum : q 0 + q 1 = ∑ t ∈ s, p t := by rw [← Fin.sum_univ_two q]; exact hsat
  rw [← hAunion, hcb]
  linarith [hle 0, hle 1, hqsum]
end FairChores
