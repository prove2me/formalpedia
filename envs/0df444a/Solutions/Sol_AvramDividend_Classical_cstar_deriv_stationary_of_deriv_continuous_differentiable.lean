-- Prove2me | solution 1 for AvramDividend.Classical.cstar_deriv_stationary_of_deriv_continuous_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:21:38.608223+00:00
-- url     : https://prove2.me/submissions/07a8ce11-ea5d-433a-b31b-bf57f30162c5

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (hpos : 0 < (cstar W).toReal)
    (hdiff : DifferentiableAt ℝ (deriv W) (cstar W).toReal) :
    HasDerivAt (deriv W) 0 (cstar W).toReal := by
  rcases cstar_toReal_zero_or_minimal_of_deriv_continuous W hcont with
    hz | ⟨hp, hmin⟩
  · exact False.elim ((ne_of_gt hpos) hz)
  · have hloc : IsLocalMin (deriv W) (cstar W).toReal := by
      change ∀ᶠ x in 𝓝 (cstar W).toReal,
        deriv W (cstar W).toReal ≤ deriv W x
      filter_upwards [isOpen_Ioi.mem_nhds hp] with x hx
      exact hmin x hx
    have heq := hloc.deriv_eq_zero
    simpa only [heq] using hdiff.hasDerivAt
