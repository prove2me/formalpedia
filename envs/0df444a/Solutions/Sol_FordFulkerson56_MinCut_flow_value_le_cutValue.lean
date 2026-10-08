-- Prove2me | solution 1 for FordFulkerson56.MinCut.flow_value_le_cutValue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:28:44.554649+00:00
-- url     : https://prove2.me/submissions/a342b6eb-969c-4d7c-8c27-b6bbab002f7e

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting

open FordFulkerson56.MinCut in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    ∀ f, IsFlow N f → ∀ D : Finset E, IsDisconnecting N D → value f ≤ cutValue N D := by
  intro f hf D hD
  obtain ⟨hnn, hch, hcap⟩ := hf
  have key : ∀ C : Finset E, f C ≤ ∑ e ∈ D, (if e ∈ C then f C else 0) := by
    intro C
    by_cases h0 : f C = 0
    · rw [h0]
      exact Finset.sum_nonneg (fun e _ => by split_ifs <;> exact le_refl _)
    · obtain ⟨e, he⟩ := hD C (hch C h0)
      rw [Finset.mem_inter] at he
      have hle : (if e ∈ C then f C else 0) ≤ ∑ e ∈ D, (if e ∈ C then f C else 0) :=
        Finset.single_le_sum (f := fun e => if e ∈ C then f C else 0)
          (fun e _ => by split_ifs <;> simp [hnn C]) he.2
      simpa [he.1] using hle
  calc value f = ∑ C, f C := rfl
    _ ≤ ∑ C, ∑ e ∈ D, (if e ∈ C then f C else 0) := Finset.sum_le_sum (fun C _ => key C)
    _ = ∑ e ∈ D, ∑ C, (if e ∈ C then f C else 0) := Finset.sum_comm
    _ = ∑ e ∈ D, load f e := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        unfold load
        rw [Finset.sum_filter]
    _ ≤ ∑ e ∈ D, N.cap e := Finset.sum_le_sum (fun e _ => hcap e)
    _ = cutValue N D := rfl
