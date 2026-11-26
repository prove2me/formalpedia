-- Prove2me | solution 1 for Eden.squaredRadiusEvolution_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:15.784384+00:00
-- url     : https://prove2.me/submissions/8a98cf89-d41a-4425-b61a-3824f64503c3

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_amplitudeSq_pos
import Theorems.Thm_Eden_mul_amplitudeSq

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ squaredRadiusEvolution t s := by
  rw [← mul_amplitudeSq ht s]
  exact mul_nonneg hs (le_of_lt (amplitudeSq_pos ht hs))
end Eden
