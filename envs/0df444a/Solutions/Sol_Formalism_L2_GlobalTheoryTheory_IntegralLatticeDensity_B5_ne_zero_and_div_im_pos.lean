-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ne_zero_and_div_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:07.386803+00:00
-- url     : https://prove2.me/submissions/f5e1c648-bb1b-41d2-9a55-6a3a4feaa00a

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_NormArea
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_conj_mul_im_eq_normSq_mul_div_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    a ≠ 0 ∧ 0 < (b / a).im := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  refine ⟨ha, ?_⟩
  rw [conj_mul_im_eq_normSq_mul_div_im a b ha] at hab
  exact pos_of_mul_pos_right hab (Complex.normSq_nonneg a)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
