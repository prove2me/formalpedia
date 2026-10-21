-- Prove2me | solution 2 for ConsHalving.Additive.half_case
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:23:27.351274+00:00
-- url     : https://prove2.me/submissions/2443eb04-01aa-4415-b985-5dd32ca3bf3e

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

set_option autoImplicit false
open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (hnm : m ≤ n) :
    IsConsensusHalving u (fun _ => 1 / 2) ∧
      numCuts (fun _ : Fin m => (1 / 2 : ℝ)) = min n m := by
  classical
  refine ⟨⟨fun j => ⟨by norm_num, by norm_num⟩, fun i => ?_⟩, ?_⟩
  · unfold util
    exact Finset.sum_congr rfl fun j _ => by norm_num
  · have hc : ∀ j : Fin m, IsCut (fun _ : Fin m => (1 / 2 : ℝ)) j :=
      fun j => ⟨by norm_num, by norm_num⟩
    unfold numCuts
    rw [Finset.filter_true_of_mem (fun j _ => hc j)]
    simp [min_eq_right hnm]
