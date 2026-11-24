-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.sub_homogeneousComponent_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:15.897379+00:00
-- url     : https://prove2.me/submissions/dd8023bb-0d26-46b4-bff8-d21f7fc87658

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
theorem _root_.solution {W : MvPolynomial σ S} {j : ℕ} (hW : W ∈ Io S σ ^ j) :
    W - homogeneousComponent j W ∈ Io S σ ^ (j + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hW ⊢
  intro x hx
  rw [coeff_sub, coeff_homogeneousComponent]
  split_ifs with h
  · simp
  · have : x.degree < j := by omega
    simp [hW x this]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
