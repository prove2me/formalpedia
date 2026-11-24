-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.cj_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:55.134409+00:00
-- url     : https://prove2.me/submissions/b43f33a9-7440-4295-a60a-0e888460964f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA

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
theorem _root_.solution (a : E) : cj (-a) = -cj a := eq_of_emb fun φ => by rw [hcj, map_neg, star_neg, map_neg, hcj]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
