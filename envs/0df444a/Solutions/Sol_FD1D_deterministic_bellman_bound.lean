-- Prove2me | solution 1 for FD1D.deterministic_bellman_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:06.433389+00:00
-- url     : https://prove2.me/submissions/e14ee95e-7598-4a06-92bb-3b3a183f1bb9

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_nodeMass_nonneg
import Theorems.Thm_FD1D_hazardEnergy_root
import Theorems.Thm_FD1D_bellman_global_bound
import Theorems.Thm_FD1D_bellman_cost_eq_drift_div

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (L : ℕ) {a m : ℝ} (N q h t Z B : ∀ d, DyadicNode d → ℝ)
    (ha : 0 < a) (hm : 0 < m)
    (ht : ∀ d v, t d v = (nodeMass d v - q d v) / a)
    (hZ : ∀ d v, Z d v = nodeMass d v / (N d v + a))
    (hroot : h 0 dyadicRoot = 1 / m)
    (hlocal : ∀ d, d < L → ∀ v,
      childAverage (fun d v => t d v * Z d v) d v +
          childAverage B d v - B d v ≥
        (childAverage (fun d v => (h d v) ^ 2) d v -
          (h d v) ^ 2) / 100)
    (hleaf : ∀ v : DyadicNode L, B L v ≤ 0)
    (hBroot : -(1 / (3 * m ^ 2)) ≤ B 0 dyadicRoot) :
    bellmanDrift L a N q ≥
      a * (hazardEnergy h L / 100 - 103 / (300 * m ^ 2)) := by
  have hglobal := bellman_global_bound L h t Z B hlocal
  rw [bellman_cost_eq_drift_div L a N q t Z ht hZ] at hglobal
  have hleafsum : weightedLevel B L ≤ 0 := by
    apply Finset.sum_nonpos
    intro v _
    exact mul_nonpos_of_nonneg_of_nonpos (nodeMass_nonneg L v) (hleaf v)
  have hH0 : hazardEnergy h 0 = 1 / m ^ 2 := by
    rw [hazardEnergy_root, hroot]
    field_simp
  rw [hH0] at hglobal
  have hlower :
      hazardEnergy h L / 100 - 103 / (300 * m ^ 2) ≤
        bellmanDrift L a N q / a := by
    have hpre :
        (hazardEnergy h L - 1 / m ^ 2) / 100 -
            1 / (3 * m ^ 2) ≤ bellmanDrift L a N q / a := by
      linarith
    have heq :
        (hazardEnergy h L - 1 / m ^ 2) / 100 -
            1 / (3 * m ^ 2) =
          hazardEnergy h L / 100 - 103 / (300 * m ^ 2) := by
      field_simp
      ring
    rwa [← heq]
  have := (le_div_iff₀ ha).mp hlower
  nlinarith
end FD1D
