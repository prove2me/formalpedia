-- Prove2me | solution 1 for CohnElkies.minusPolynomial_translation_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/a4540942-d3f9-4078-ba59-3e2250324094

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_minusPolynomial_add_sub
import Theorems.Thm_CohnElkies_minusSaddleLinearCoefficient_norm_le
import Theorems.Thm_CohnElkies_minusSaddleQuadraticCoefficient_norm_le
import Theorems.Thm_CohnElkies_saddle_cubic_translation_norm_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (ε u T : ℝ) :
    ‖minusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  let z : ℂ := Complex.I * (u : ℂ)
  have hz : ‖z‖ = |u| := by
    try dsimp [z]
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hA :
      ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
        3 * (1 + |u|) ^ 2 := by
    simpa [hz] using! minusSaddleLinearCoefficient_norm_le z
  have hB :
      ‖1 - 3 * Complex.I * z‖ ≤
        3 * (1 + |u|) ^ 2 := by
    simpa [hz] using! minusSaddleQuadraticCoefficient_norm_le z
  have hidentity :
      minusPolynomial ε ((T : ℂ) + z) -
          minusPolynomial ε z =
        (T : ℂ) * (2 * z - Complex.I * (1 + 3 * z ^ 2)) +
          (T : ℂ) ^ 2 * (1 - 3 * Complex.I * z) +
            (-Complex.I) * (T : ℂ) ^ 3 := by
    rw [add_comm (T : ℂ) z,
      minusPolynomial_add_sub]
    ring
  change
    ‖minusPolynomial ε ((T : ℂ) + z) -
        minusPolynomial ε z‖ ≤ _
  rw [hidentity]
  exact saddle_cubic_translation_norm_le u T
    (2 * z - Complex.I * (1 + 3 * z ^ 2))
    (1 - 3 * Complex.I * z) (-Complex.I)
    hA hB (by simp)
end CohnElkies
