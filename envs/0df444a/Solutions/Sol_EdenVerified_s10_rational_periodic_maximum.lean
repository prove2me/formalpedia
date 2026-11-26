-- Prove2me | solution 1 for EdenVerified.s10_rational_periodic_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:59.514509+00:00
-- url     : https://prove2.me/submissions/ac607f6b-a9db-42d7-89fb-26ec20eb7b60

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_frequency_periodic_asymptotic_isGreatest
import Theorems.Thm_Eden_frequency_periodic_finiteTime_isGreatest
import Theorems.Thm_Eden_rational_frequency_torus_period
import Theorems.Thm_Eden_torus_subset_frequencyPeriodicSet


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (ν : ℚ) (_hν : 0 < ν) :
    torus ⊆ frequencyPeriodicSet c ν ∧
    (∀ p ∈ torus, 0 < 2 * Real.pi * ν.den ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c ν t p) (2 * Real.pi * ν.den)) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c)) :=
  ⟨torus_subset_frequencyPeriodicSet c ν, fun p hp => rational_frequency_torus_period c ν hp,
    frequency_periodic_asymptotic_isGreatest hc ν,
    fun t ht => frequency_periodic_finiteTime_isGreatest hc ν ht⟩
end EdenVerified
