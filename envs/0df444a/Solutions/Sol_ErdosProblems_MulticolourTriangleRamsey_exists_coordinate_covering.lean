-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_coordinate_covering
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/8e64c166-e3ad-4629-b135-3da3620e818f

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_saturated_matrix_ceil
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_saturated_coordinate_covering

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 2 ≤ H) :
    ∃ f g : (Fin (saturatedMatrixRows H) → Fin H) →
        (Fin (saturatedMatrixRows H) → Fin H),
      IsCoordinateCovering f g := by
  obtain ⟨A, hA⟩ := exists_saturated_matrix_ceil H hH
  have hwidth : saturatedMatrixWidth H ≤ saturatedMatrixRows H := by
    dsimp [saturatedMatrixRows]
    nlinarith [sq_nonneg (saturatedMatrixWidth H : ℤ)]
  exact saturated_coordinate_covering A hA (by omega) hwidth
end ErdosProblems.MulticolourTriangleRamsey
