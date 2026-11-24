-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.ed_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:31:14.036887+00:00
-- url     : https://prove2.me/submissions/c9922984-f0bf-4b5a-a714-e83d9c92004a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_tr_ed_int
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
theorem _root_.solution (i : Free.ChooseBasisIndex ℤ (𝓞 E)) : ed E i ∈ Dinv E := mem_Dinv.mpr fun c => ⟨_, tr_ed_int c i⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
