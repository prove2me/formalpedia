-- Prove2me | solution 1 for ConsensusHalvingItems.Additive.half_partition_of_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:34:12.815705+00:00
-- url     : https://prove2.me/submissions/0c47b631-f4a6-4e91-8fc1-1d0a074cfcb7

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving
import Definitions.Def_ConsensusHalvingItems_Additive_numCuts

open ConsensusHalvingItems.Additive in
theorem solution {n m : ℕ} (u : Fin n → Fin m → ℚ) (hmn : m ≤ n) :
    IsConsensusHalving u (fun _ => (1 / 2 : ℚ)) ∧
      numCuts (fun _ : Fin m => (1 / 2 : ℚ)) = min n m := by
  refine ⟨⟨fun j => by norm_num, fun i => ?_⟩, ?_⟩
  · unfold additiveUtil
    norm_num
  · unfold numCuts
    rw [min_eq_right hmn]
    norm_num
