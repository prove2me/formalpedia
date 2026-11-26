-- Prove2me | solution 1 for FD1D.hazard_energy_bound_of_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:55:59.712506+00:00
-- url     : https://prove2.me/submissions/b918e7b1-ddfd-4a08-bcc1-14eaab2bbd1e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_hazardEnergy_root
import Theorems.Thm_FD1D_hazard_energy_bound

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (L : ℕ) {a m : ℝ} (h b : ∀ d, DyadicNode d → ℝ)
    (hm : m ≠ 0) (hroot : h 0 dyadicRoot = 1 / m)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 ≤ 2 * a ^ 2 *
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - 1 / m ^ 2) := by
  have hbound := hazard_energy_bound L a h b hlocal
  have hH0 : hazardEnergy h 0 = 1 / m ^ 2 := by
    rw [hazardEnergy_root, hroot]
    field_simp
  rwa [hH0] at hbound
end FD1D
