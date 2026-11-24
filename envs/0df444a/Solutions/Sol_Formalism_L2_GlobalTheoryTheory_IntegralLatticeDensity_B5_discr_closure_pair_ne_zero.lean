-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_closure_pair_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:59.811834+00:00
-- url     : https://prove2.me/submissions/39c1a796-d958-4002-84c4-2b913fddb594

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_NormArea
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ne_zero_and_div_im_pos
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_discr_closure_pair


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
    discr (AddSubgroup.closure {a, b}) ≠ 0 := by
  obtain ⟨ha, hpos⟩ := ne_zero_and_div_im_pos a b hab
  rw [discr_closure_pair a b hpos]
  have hpi : (2 * Real.pi / a : ℂ) ≠ 0 := by
    refine div_ne_zero ?_ ha
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero (pow_ne_zero _ hpi) (pow_ne_zero _ (ModularForm.eta_ne_zero hpos))
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
