-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.eb_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:56.365608+00:00
-- url     : https://prove2.me/submissions/80245164-7234-4ca4-b44b-a42fa9f4dd37

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_tr_ed_eb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution (z : E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z i = Algebra.trace ℚ E (ed E i * z) := by
  have h : (integralBasis E).coord i =
      (Algebra.trace ℚ E).comp (LinearMap.mulLeft ℚ (ed E i)) := (integralBasis E).ext fun j => by
    show (integralBasis E).repr (integralBasis E j) i = Algebra.trace ℚ E (ed E i * integralBasis E j)
    rw [Module.Basis.repr_self, tr_ed_eb, Finsupp.single_apply]
  exact LinearMap.congr_fun h z
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
