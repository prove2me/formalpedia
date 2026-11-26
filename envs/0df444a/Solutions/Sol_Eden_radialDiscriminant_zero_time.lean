-- Prove2me | solution 1 for Eden.radialDiscriminant_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:39.587903+00:00
-- url     : https://prove2.me/submissions/78c7426f-6268-49a1-83ca-5363c6217544

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
theorem _root_.solution (s : ℝ) : radialDiscriminant 0 s = 1 := by
  simp [radialDiscriminant]
end Eden
