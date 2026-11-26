-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:27.503063+00:00
-- url     : https://prove2.me/submissions/76189641-d4b8-4d97-b9a2-25f17d68382e

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
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_at_two

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) :
    squaredRadiusEvolution t 0 = 0 := by
  simp [squaredRadiusEvolution]
end Eden
