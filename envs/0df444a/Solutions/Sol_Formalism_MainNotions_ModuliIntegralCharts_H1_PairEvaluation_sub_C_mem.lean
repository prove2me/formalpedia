-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.sub_C_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:57.934883+00:00
-- url     : https://prove2.me/submissions/fc0e583f-0d95-4d59-af04-0b14d2b3df26

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
theorem _root_.solution (p : MvPolynomial σ S) : p - C (coeff 0 p) ∈ Io S σ := by
  have h := (mem_pow_idealOfVars_iff' (σ := σ) (R := S) 1 (p - C (coeff 0 p))).2 (fun x hx => by
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    subst hx0
    simp)
  simpa using h
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
