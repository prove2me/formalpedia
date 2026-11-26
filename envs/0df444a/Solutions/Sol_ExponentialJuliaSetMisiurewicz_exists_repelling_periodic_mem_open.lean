-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exists_repelling_periodic_mem_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:01.509624+00:00
-- url     : https://prove2.me/submissions/e7f48a93-f478-4c6c-b111-c866b247c6dc

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_repelling_near_real_preimage
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_nonzero_mem_open
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_iterate_eq_nonzero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, ∃ n : ℕ,
      0 < n ∧ expIterate n p = p ∧ 1 < ‖deriv (expIterate n) p‖ := by
  obtain ⟨b, hb, hb0⟩ := exists_nonzero_mem_open hU hUne
  have hVopen : IsOpen (U \ {0}) := hU.sdiff isClosed_singleton
  have hVne : (U \ {0}).Nonempty := ⟨b, hb, by simpa using hb0⟩
  -- The covering theorem supplies a preimage of 10 inside the chosen open set.
  obtain ⟨m, _, a, ha, hm⟩ := exists_iterate_eq_nonzero hVopen hVne
    (w := 10) (by norm_num)
  have ha0 : a ≠ 0 := by simpa using ha.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU a ha.1
  obtain ⟨p, hp, n, hn, hperiod, hrepel⟩ := exists_repelling_near_real_preimage ha0 hm hε
  exact ⟨p, hball hp, n, hn, hperiod, hrepel⟩
end ExponentialJuliaSetMisiurewicz
