-- Prove2me | solution 2 for FlowsNetworks.MaxFlow.minimal_cuts_union_inter
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:10:11.063104+00:00
-- url     : https://prove2.me/submissions/4c4cbdc5-937d-4b09-8e1b-cf4ce8212862

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network
set_option autoImplicit false
open FlowsNetworks.MaxFlow

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (X Y : Finset N)
    (hX : IsMinCut G s t X) (hY : IsMinCut G s t Y) :
    IsMinCut G s t (X ∪ Y) ∧ IsMinCut G s t (X ∩ Y) := by
  have hcap : ∀ (Z : Finset N), cutCapacity G Z =
      ∑ p ∈ G.arcs, if (p.1 ∈ Z ∧ p.2 ∉ Z) then G.cap p.1 p.2 else 0 := by
    intro Z
    unfold cutCapacity arcSum arcsBetween
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    simp [Finset.mem_compl]
  have hsub : cutCapacity G (X ∪ Y) + cutCapacity G (X ∩ Y) ≤ cutCapacity G X + cutCapacity G Y := by
    rw [hcap, hcap, hcap, hcap, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h0 := G.cap_nonneg p hp
    by_cases a : p.1 ∈ X <;> by_cases b : p.2 ∈ X <;> by_cases c : p.1 ∈ Y <;> by_cases d : p.2 ∈ Y <;>
      simp [a, b, c, d, h0]
  obtain ⟨hsX, htX, hmX⟩ := hX
  obtain ⟨hsY, htY, hmY⟩ := hY
  have hU1 : s ∈ X ∪ Y := Finset.mem_union_left _ hsX
  have hU2 : t ∉ X ∪ Y := by simp [htX, htY]
  have hI1 : s ∈ X ∩ Y := Finset.mem_inter.2 ⟨hsX, hsY⟩
  have hI2 : t ∉ X ∩ Y := by simp [htX]
  have eXY : cutCapacity G X = cutCapacity G Y := le_antisymm (hmX Y hsY htY) (hmY X hsX htX)
  have lU := hmX _ hU1 hU2
  have lI := hmX _ hI1 hI2
  have eU : cutCapacity G (X ∪ Y) = cutCapacity G X := by linarith
  have eI : cutCapacity G (X ∩ Y) = cutCapacity G X := by linarith
  refine ⟨⟨hU1, hU2, ?_⟩, ⟨hI1, hI2, ?_⟩⟩
  · intro Z hs ht; rw [eU]; exact hmX Z hs ht
  · intro Z hs ht; rw [eI]; exact hmX Z hs ht
