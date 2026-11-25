-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.casimir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:53.523177+00:00
-- url     : https://prove2.me/submissions/5b4e6bfa-0ddd-4396-b23e-2b9cb12ca2ce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_ortho

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
open scoped Classical
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution : ∑ i, ed E i * integralBasis E i = 1 := by
  refine eq_of_emb fun σ => ?_
  rw [map_sum, map_one]
  simp_rw [map_mul]
  rw [ortho σ σ, if_pos rfl]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
