-- Prove2me | solution 1 for ConsHalving.Additive.eq_1_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:59:19.002376+00:00
-- url     : https://prove2.me/submissions/ad167256-8f4a-4b1b-b078-d3d136d7904a

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (x : Fin m → ℝ) :
    (∀ i, util u i x = util u i (fun j => 1 - x j)) ↔
      ∀ i, ∑ j, x j * u i j = (1 / 2) * ∑ j, u i j := by
  have key : ∀ i, util u i (fun j => 1 - x j) = ∑ j, u i j - ∑ j, x j * u i j := by
    intro i
    unfold util
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine forall_congr' fun i => ?_
  rw [key]
  unfold util
  constructor <;> intro h <;> linarith
