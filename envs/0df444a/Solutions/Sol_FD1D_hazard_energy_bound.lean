-- Prove2me | solution 1 for FD1D.hazard_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:53.914951+00:00
-- url     : https://prove2.me/submissions/67cbd648-7fcc-41b9-897c-799ec7607aa6

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_nodeMass_nonneg
import Theorems.Thm_FD1D_hazard_energy_telescope

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (L : ℕ) (a : ℝ)
    (h b : ∀ d, DyadicNode d → ℝ)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 ≤ 2 * a ^ 2 *
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by
  have hs :
      internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
        ∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v * (2 * a ^ 2 *
            (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left
      (hlocal d (Finset.mem_range.mp hd) v) (nodeMass_nonneg d v)
  calc
    internalWeightedSum (fun d v => (b d v) ^ 2) L
        ≤ _ := hs
    _ = 2 * a ^ 2 *
        (∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = 2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by
      rw [hazard_energy_telescope]
end FD1D
