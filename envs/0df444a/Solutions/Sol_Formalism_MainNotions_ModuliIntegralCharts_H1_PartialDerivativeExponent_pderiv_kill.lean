-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.pderiv_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:22.27922+00:00
-- url     : https://prove2.me/submissions/d67959de-29fd-4b43-a482-87dda3473661

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_mem_subV

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
open MvPowerSeries
variable {σ : Type}
variable {k : Type} [CommRing k]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
theorem _root_.solution {V : Set σ} {i : σ} (hi : i ∉ V) {f : MvPowerSeries σ k} (hf : f ∈ subV k V) :
    pderiv k i f = 0 := by
  rw [mem_subV] at hf
  ext e
  rw [coeff_pderiv, map_zero]
  by_cases h : coeff (e + Finsupp.single i 1) f = 0
  · rw [h, zero_mul]
  · exfalso
    apply hi
    apply hf _ h i
    rw [Finsupp.mem_support_iff]
    simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
