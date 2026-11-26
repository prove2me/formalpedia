-- Prove2me | solution 1 for Eden.radialDiscriminant_at_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:26.930663+00:00
-- url     : https://prove2.me/submissions/ccc9bbb5-79dc-414c-b8ab-a82a382a75c5

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.radialDiscriminant_at_zero

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) : radialDiscriminant t 2 = 1 := by
  dsimp [radialDiscriminant]
  ring
end Eden
