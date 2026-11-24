-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.cj_mem_Dinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:57.562813+00:00
-- url     : https://prove2.me/submissions/ac79e1e2-c3fd-42b2-bc08-7fc7a649cf40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_cj
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_trace_cj
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_integral
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_mem_Dinv

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
theorem _root_.solution {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
    {z : E} (hz : z ∈ Dinv E) : cj z ∈ Dinv E := by
  rw [mem_Dinv] at hz ⊢
  intro c
  obtain ⟨c', hc'⟩ := cj_integral hcj c
  obtain ⟨m, hm⟩ := hz c'
  refine ⟨m, ?_⟩
  rw [← hm, hc', ← trace_cj hcj (z * cj c), cj_mul hcj, cj_cj hcj]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
