-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.tr_ed_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:55.501103+00:00
-- url     : https://prove2.me/submissions/dd7a23b8-9157-450f-855c-8a55c307d2ce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_eb_repr

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
theorem _root_.solution (c : 𝓞 E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (ed E i * (c : E)) = ((RingOfIntegers.basis E).repr c i : ℚ) := by
  rw [← eb_repr]
  have h := integralBasis_repr_apply E c i
  simpa using h
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
