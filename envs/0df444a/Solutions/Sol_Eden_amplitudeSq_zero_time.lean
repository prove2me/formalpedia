-- Prove2me | solution 1 for Eden.amplitudeSq_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:50.787851+00:00
-- url     : https://prove2.me/submissions/1a111360-ee77-40b2-ab60-92c76e349174

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_zero_time

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) : amplitudeSq 0 s = 1 := by
  simp [amplitudeSq]
end Eden
