-- Prove2me | solution 1 for Eden.amplitudeSq_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:16.807218+00:00
-- url     : https://prove2.me/submissions/ee743b22-42f8-4c38-9dd0-1eb95edf9dcc

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
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_two

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) :
    amplitudeSq t 0 = Real.exp (-4 * t) := by
  simp [amplitudeSq]
  ring
end Eden
