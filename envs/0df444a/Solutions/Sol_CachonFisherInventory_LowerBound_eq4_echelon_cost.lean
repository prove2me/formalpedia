-- Prove2me | solution 1 for CachonFisherInventory.LowerBound.eq4_echelon_cost
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:55:57.362901+00:00
-- url     : https://prove2.me/submissions/7ee351fe-df34-4008-a67e-3daaf3881107

import Mathlib
import Definitions.Def_CachonFisherInventory_LowerBound_Physical

open CachonFisherInventory.LowerBound
open CachonFisherInventory.LowerBound

theorem solution(P : Parameters) (s : Stock P) :
    actualCost P s = P.hs * (echelon P s : ℝ) +
      ∑ i, (P.hr * onHand s i + (P.hs + P.pr) * backlog s i) := by
  have key : ∀ i, (retailerNet s i : ℝ) = onHand s i - backlog s i := by
    intro i
    unfold onHand backlog
    rcases le_total (retailerNet s i : ℝ) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hk : ∑ i, (retailerNet s i : ℝ) = ∑ i, onHand s i - ∑ i, backlog s i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => key i)
  unfold actualCost echelon inventoryPosition
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  first
  | linear_combination (-P.hs) * hk
  | linear_combination P.hs * hk
