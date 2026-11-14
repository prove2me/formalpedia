-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.recourse_path_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:19.779297+00:00
-- url     : https://prove2.me/submissions/fe0d3bb9-2b38-4f39-ab55-f43448674579

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem card_pre (D : Finset (Fin n)) (r : ℕ) : (pre D r).card = min r D.card := by
  rw [pre, List.toFinset_card_of_nodup (List.Nodup.sublist (List.take_sublist r _)
    D.nodup_toList), List.length_take, Finset.length_toList]

theorem pre_mono (D : Finset (Fin n)) {r r' : ℕ} (h : r ≤ r') : pre D r ⊆ pre D r' := by
  intro x hx
  exact List.mem_toFinset.mpr ((List.take_prefix_take_left h).subset (List.mem_toFinset.mp hx))

end ConsistentSubmodular.Checkpoints

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem solution (C A : Finset (Fin n)) {r r' : ℕ} (h : r ≤ r') :
    recourse (path C A r') (path C A r) ≤ 2 * (r' - r) := by
  have hP := pre_mono (C \ A) h
  have hQ := pre_mono (A \ C) h
  have hsub : (path C A r' \ path C A r) ∪ (path C A r \ path C A r') ⊆
      (pre (A \ C) r' \ pre (A \ C) r) ∪ (pre (C \ A) r' \ pre (C \ A) r) := by
    intro x hx
    simp only [path, Finset.mem_union, Finset.mem_sdiff] at hx ⊢
    have hP' := @hP x
    have hQ' := @hQ x
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_sdiff_of_subset hQ, Finset.card_sdiff_of_subset hP, card_pre, card_pre,
    card_pre, card_pre] at hc
  unfold recourse
  omega

end
