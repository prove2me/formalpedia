-- Prove2me | solution 1 for AvramDividend.Classical.deriv_deriv_eq_zero_of_mem_cstarSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:11:59.827314+00:00
-- url     : https://prove2.me/submissions/b0a0d9cf-9a8f-4be1-a30d-be1bc6a68c74

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W) : deriv (deriv W) a = 0 := by
  change 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x at ha
  obtain ⟨ha0, hmin⟩ := ha
  have hloc : IsLocalMin (deriv W) a := by
    change ∀ᶠ x in 𝓝 a, deriv W a ≤ deriv W x
    filter_upwards [isOpen_Ioi.mem_nhds ha0] with x hx
    exact hmin x hx
  exact hloc.deriv_eq_zero
