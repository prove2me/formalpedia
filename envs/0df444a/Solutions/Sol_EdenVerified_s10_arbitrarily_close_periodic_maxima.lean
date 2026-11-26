-- Prove2me | solution 1 for EdenVerified.s10_arbitrarily_close_periodic_maxima
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:02.223973+00:00
-- url     : https://prove2.me/submissions/9053affe-4a2f-4c2d-8f7c-500f9add8212

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_exists_nearby_frequency_periodic_maximum


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ)-Real.sqrt 2| < ε ∧
      IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
      ∀ t : ℝ, 0 < t →
        IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c) :=
  exists_nearby_frequency_periodic_maximum hc hε
end EdenVerified
