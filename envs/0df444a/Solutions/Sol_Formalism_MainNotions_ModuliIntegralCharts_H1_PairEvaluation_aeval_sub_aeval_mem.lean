-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_sub_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:29.994612+00:00
-- url     : https://prove2.me/submissions/97c32ab2-6998-4431-a280-43a8d2d6056e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_mem_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_sub_C_mem

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
theorem _root_.solution (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (p : MvPolynomial σ S) : aeval g p - aeval g' p ∈ Io S τ := by
  have h0 : p - C (coeff 0 p) ∈ Io S σ ^ 1 := by simpa using sub_C_mem p
  have h1 := aeval_mem_pow g hg 1 h0
  have h2 := aeval_mem_pow g' hg' 1 h0
  have h3 := sub_mem (by simpa using h1) (by simpa using h2)
  simpa [map_sub, aeval_C] using h3
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
