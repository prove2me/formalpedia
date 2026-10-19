-- Prove2me | solution 1 for CompactnessConjecture.quadrangle_density_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/17cb094f-8aa8-480b-9cb1-24e6ffb642fe

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution (q : ℕ) :
    (quadrangleVertexCount q : ℝ) ^ 4 ≤
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 := by
  have hnonneg :
      0 ≤ 32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
        ((q : ℝ) ^ 2 + 1) ^ 3 := by
    positivity
  have hidentity :
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 -
          (quadrangleVertexCount q : ℝ) ^ 4 =
        32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
          ((q : ℝ) ^ 2 + 1) ^ 3 := by
    simp only [quadrangleVertexCount, quadrangleEdgeCount,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
    ring
  linarith
end CompactnessConjecture
