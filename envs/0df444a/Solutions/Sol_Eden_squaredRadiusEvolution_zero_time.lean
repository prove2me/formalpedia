-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:10.708727+00:00
-- url     : https://prove2.me/submissions/bb64f39e-257c-4c5e-a0c8-81a5808a3e9e

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_zero_time
attribute [local simp] Eden.radialDiscriminant_zero_time

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) :
    squaredRadiusEvolution 0 s = s := by
  simp [squaredRadiusEvolution]
end Eden
