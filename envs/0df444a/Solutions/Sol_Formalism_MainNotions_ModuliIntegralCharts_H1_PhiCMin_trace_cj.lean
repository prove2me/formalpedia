-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.trace_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:57.765604+00:00
-- url     : https://prove2.me/submissions/b31a25ab-6896-40d0-b9dc-3314568fff39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_trace_sum

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
variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution (z : E) : Algebra.trace ℚ E (cj z) = Algebra.trace ℚ E z := by
  apply Rat.cast_injective (α := ℂ)
  rw [trace_sum, trace_sum]
  simp_rw [hcj]
  rw [← star_sum, ← trace_sum]
  exact map_ratCast (starRingEnd ℂ) _
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
