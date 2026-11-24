-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_closure_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:03.024891+00:00
-- url     : https://prove2.me/submissions/93c65d1e-8c56-427a-bbde-d98442614f80

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_jac_discr

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
theorem _root_.solution (a b : ℂ) (hab : 0 < (b / a).im) :
    discr (AddSubgroup.closure {a, b}) = (2 * Real.pi / a) ^ 12 * ModularForm.eta (b / a) ^ 24 := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  have h := jac_discr a (b / a) ha hab
  rw [show a * (b / a) = b by field_simp] at h
  exact h
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
