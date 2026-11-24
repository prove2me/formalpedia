-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eq_zero_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:15.1578+00:00
-- url     : https://prove2.me/submissions/b416abc0-a7ea-4741-9386-77fa0f8d59e3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
variable {σ τ : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j)
    (hm : h ∈ Io S σ ^ (j + 1)) : h = 0 := by
  ext e
  rw [coeff_zero]
  by_contra hne
  have h1 := (mem_pow_idealOfVars_iff (j + 1) h).1 hm e (mem_support_iff.2 hne)
  have h2 : e.degree = j := by
    have := hh hne
    rw [Finsupp.degree_eq_weight_one]
    exact this
  omega
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
