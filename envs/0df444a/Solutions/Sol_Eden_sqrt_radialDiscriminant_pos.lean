-- Prove2me | solution 1 for Eden.sqrt_radialDiscriminant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:32.188152+00:00
-- url     : https://prove2.me/submissions/43d14957-a9b2-4bc5-9126-d1f90a11eb05

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_pos

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    0 < Real.sqrt (radialDiscriminant t s) :=
  Real.sqrt_pos.2 (radialDiscriminant_pos ht s)
end Eden
