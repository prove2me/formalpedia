-- Prove2me | solution 1 for Eden.mul_amplitudeSq_of_discriminant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:05.774339+00:00
-- url     : https://prove2.me/submissions/802f6316-584e-41e1-9960-053348b02355

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    s * amplitudeSq t s = squaredRadiusEvolution t s := by
  have hR := Real.sqrt_pos.2 hD
  have hR₀ : Real.sqrt (radialDiscriminant t s) ≠ 0 := ne_of_gt hR
  have hR₁ : Real.sqrt (radialDiscriminant t s) + 1 ≠ 0 := by linarith
  have hsq : Real.sqrt (radialDiscriminant t s) ^ 2 =
      Real.exp (-4 * t) + (1 - Real.exp (-4 * t)) * (s - 1) ^ 2 :=
    Real.sq_sqrt (le_of_lt hD)
  dsimp [amplitudeSq, squaredRadiusEvolution]
  field_simp
  simp only [neg_mul] at hsq
  nlinarith
end Eden
