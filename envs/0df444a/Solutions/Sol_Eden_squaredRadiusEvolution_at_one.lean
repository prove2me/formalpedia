-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_at_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:37.227943+00:00
-- url     : https://prove2.me/submissions/64443683-9e88-4787-98ec-e9505043e48e

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_amplitudeSq_zero_time
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_zero_time

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) :
    squaredRadiusEvolution t 1 = 1 := by
  simp [squaredRadiusEvolution]
end Eden
