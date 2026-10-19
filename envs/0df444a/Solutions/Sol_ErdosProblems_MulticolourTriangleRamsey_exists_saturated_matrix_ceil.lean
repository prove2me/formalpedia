-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_saturated_matrix_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/5bb1146a-c7fe-42bf-adcd-0e165e0aa4e0

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_saturated_matrix

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 2 ≤ H) :
    ∃ A : Fin (saturatedMatrixRows H) →
        (Fin (saturatedMatrixWidth H) → Fin H) → Fin H,
      IsSaturated A := by
  have hwidth :
      2 * (H : ℝ) * Real.log (H : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    exact Nat.le_ceil _
  simpa [saturatedMatrixRows] using
    exists_saturated_matrix H (saturatedMatrixWidth H) hH hwidth
end ErdosProblems.MulticolourTriangleRamsey
