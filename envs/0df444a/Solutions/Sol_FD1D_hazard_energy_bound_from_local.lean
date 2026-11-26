-- Prove2me | solution 1 for FD1D.hazard_energy_bound_from_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:55:35.253661+00:00
-- url     : https://prove2.me/submissions/05c6e566-a7a0-4bb3-b9bc-0b31d4f206d7

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_hazard_energy_bound
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.weightedLevel_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (L : ℕ) {a : ℝ}
    (h b : ∀ d, DyadicNode d → ℝ) (ha : a ≠ 0)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 / (2 * a ^ 2) ≤
        childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by
  apply hazard_energy_bound L a h b
  intro d hdL v
  have hden : 0 < 2 * a ^ 2 := by positivity
  simpa [mul_comm] using (div_le_iff₀ hden).mp (hlocal d hdL v)
end FD1D
