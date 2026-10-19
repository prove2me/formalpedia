-- Prove2me | solution 1 for CompactnessConjecture.quadrangle_rpow_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/bf970b18-5d04-4450-ad3e-2272eac7624b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_quadrangle_density_certificate

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution (q : ℕ) :
    (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  apply ((by decide : Odd 3).strictMono_pow.le_iff_le).mp
  have hcubed :
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 =
          (quadrangleVertexCount q : ℝ) ^ 4 / 16 := by
    rw [mul_pow,
      ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))
        (-((4 : ℝ) / 3)) 3,
      ← Real.rpow_mul_natCast
        (by exact_mod_cast (Nat.zero_le (quadrangleVertexCount q)))
        ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    ring
  rw [hcubed]
  nlinarith [quadrangle_density_certificate q]
end CompactnessConjecture
