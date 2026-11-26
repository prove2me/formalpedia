-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_at_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:28.938875+00:00
-- url     : https://prove2.me/submissions/36d76cda-d2cb-4731-8b3a-571720489b9b

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_two

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) :
    squaredRadiusEvolution t 2 = 2 := by
  rw [squaredRadiusEvolution, radialDiscriminant_at_two]
  norm_num
end Eden
