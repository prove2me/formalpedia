-- Prove2me | solution 1 for FD1D.bellman_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:53.565986+00:00
-- url     : https://prove2.me/submissions/66a34a1f-b696-4de3-af4e-85d3c5f4bcfb

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_nodeMass_nonneg
import Theorems.Thm_FD1D_hazard_energy_telescope
import Theorems.Thm_FD1D_bellman_tree_telescope

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (L : ℕ) (h t Z B : ∀ d, DyadicNode d → ℝ)
    (hlocal : ∀ d, d < L → ∀ v,
      childAverage (fun d v => t d v * Z d v) d v +
          childAverage B d v - B d v ≥
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) / 100) :
    nonrootWeightedSum (fun d v => t d v * Z d v) L ≥
      (hazardEnergy h L - hazardEnergy h 0) / 100 +
        B 0 dyadicRoot - weightedLevel B L := by
  have hs :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => t d v * Z d v) d v +
            childAverage B d v - B d v))) ≥
      ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => (h d v) ^ 2) d v -
            (h d v) ^ 2) / 100) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left
      (hlocal d (Finset.mem_range.mp hd) v) (nodeMass_nonneg d v)
  rw [bellman_tree_telescope] at hs
  have henergy := hazard_energy_telescope h L
  rw [← henergy]
  have hdiv :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage (fun d v => (h d v) ^ 2) d v -
            (h d v) ^ 2)) / 100 =
        ∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            ((childAverage (fun d v => (h d v) ^ 2) d v -
              (h d v) ^ 2) / 100) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    ring
  calc
    (∑ d ∈ Finset.range L,
      ∑ v, nodeMass d v *
        (childAverage (fun d v => (h d v) ^ 2) d v -
          (h d v) ^ 2)) / 100 +
        B 0 dyadicRoot - weightedLevel B L
        = (∑ d ∈ Finset.range L,
            ∑ v, nodeMass d v *
              ((childAverage (fun d v => (h d v) ^ 2) d v -
                (h d v) ^ 2) / 100)) +
            B 0 dyadicRoot - weightedLevel B L := by
              rw [hdiv]
    _ ≤ nonrootWeightedSum (fun d v => t d v * Z d v) L := by
      linarith
end FD1D
