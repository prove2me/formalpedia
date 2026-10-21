-- Prove2me | solution 1 for ConsHalving.Additive.half_case
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:59:20.090621+00:00
-- url     : https://prove2.me/submissions/7381c094-9377-4248-9a44-523004f6f5b5

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

open ConsHalving.Additive

open Classical in
theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (hnm : m ≤ n) :
    IsConsensusHalving u (fun _ => 1 / 2) ∧
      numCuts (fun _ : Fin m => (1 / 2 : ℝ)) = min n m := by
  refine ⟨⟨fun j => by norm_num, fun i => ?_⟩, ?_⟩
  · unfold util
    refine Finset.sum_congr rfl fun j _ => ?_
    norm_num
  · rw [min_eq_right hnm]
    unfold numCuts
    rw [Finset.filter_true_of_mem (fun j _ => by unfold IsCut; norm_num)]
    simp
