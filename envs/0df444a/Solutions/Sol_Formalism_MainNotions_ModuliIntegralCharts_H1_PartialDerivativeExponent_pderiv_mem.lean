-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.pderiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:06:15.267267+00:00
-- url     : https://prove2.me/submissions/c1a8cbb3-88d4-4a2c-a220-c52a5f700bb1

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
theorem _root_.solution {V : Set σ} (i : σ) {f : MvPowerSeries σ k} (hf : f ∈ subV k V) :
    pderiv k i f ∈ subV k V := by
  rw [mem_subV] at hf ⊢
  intro e he j hj
  rw [coeff_pderiv] at he
  have h1 : coeff (e + Finsupp.single i 1) f ≠ 0 := left_ne_zero_of_mul he
  apply hf _ h1 j
  rw [Finsupp.mem_support_iff] at hj ⊢
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
