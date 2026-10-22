-- Prove2me | solution 1 for FlowsNetworks.MaxFlow.minimal_cuts_union_inter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:56:31.630187+00:00
-- url     : https://prove2.me/submissions/47d44a7d-f1c4-40c7-aaaa-f44b7d098415

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network
open FlowsNetworks.MaxFlow


theorem g69e_arcSum_eq {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (g : N → N → ℝ)
    (X Y : Finset N) :
    arcSum G g X Y = ∑ p ∈ G.arcs, if p.1 ∈ X ∧ p.2 ∈ Y then g p.1 p.2 else 0 := by
  unfold arcSum arcsBetween; rw [Finset.sum_filter]

theorem g69e_cut_submod {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (X Y : Finset N) :
    cutCapacity G (X ∪ Y) + cutCapacity G (X ∩ Y) ≤ cutCapacity G X + cutCapacity G Y := by
  unfold cutCapacity
  simp only [g69e_arcSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have h := G.cap_nonneg p hp
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  by_cases a1 : p.1 ∈ X <;> by_cases a2 : p.1 ∈ Y <;> by_cases b1 : p.2 ∈ X <;> by_cases b2 : p.2 ∈ Y <;>
    simp [a1, a2, b1, b2, h]

theorem g69e_sum_netFlowOut {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
    (X : Finset N) :
    ∑ x ∈ X, netFlowOut G f x = arcSum G f X Xᶜ - arcSum G f Xᶜ X := by
  have key : ∀ (q : N × N → N), ∑ x ∈ X, ∑ p ∈ G.arcs.filter (fun p => q p = x), f p.1 p.2
      = ∑ p ∈ G.arcs, if q p ∈ X then f p.1 p.2 else 0 := by
    intro q
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_ite_eq]
  unfold netFlowOut
  rw [Finset.sum_sub_distrib, key (fun p => p.1), key (fun p => p.2), g69e_arcSum_eq, g69e_arcSum_eq,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.mem_compl]
  by_cases a : p.1 ∈ X <;> by_cases b : p.2 ∈ X <;> simp [a, b]


/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Corollary 5.4 (p. 23): if `(X, X̄)` and
`(Y, Ȳ)` are minimal cuts, then `(X ∪ Y, (X ∪ Y)‾)` and `(X ∩ Y, (X ∩ Y)‾)` are also minimal
cuts. -/
theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (X Y : Finset N)
    (hX : IsMinCut G s t X) (hY : IsMinCut G s t Y) :
    IsMinCut G s t (X ∪ Y) ∧ IsMinCut G s t (X ∩ Y) := by
  obtain ⟨hsX, htX, hX⟩ := hX
  obtain ⟨hsY, htY, hY⟩ := hY
  have hsub := g69e_cut_submod G X Y
  have a1 := hX (X ∪ Y) (by simp [hsX]) (by simp [htX, htY])
  have a2 := hX (X ∩ Y) (by simp [hsX, hsY]) (by simp [htX])
  have a3 := hY X hsX htX
  refine ⟨⟨by simp [hsX], by simp [htX, htY], fun Z hs ht => ?_⟩,
    ⟨by simp [hsX, hsY], by simp [htX], fun Z hs ht => ?_⟩⟩
  · have := hX Z hs ht; linarith
  · have := hX Z hs ht; linarith

