-- Prove2me | solution 1 for EdenVerified.s10_maximising_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:30.464811+00:00
-- url     : https://prove2.me/submissions/3d0b0f58-11b8-4818-b28b-11a757abee60

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_frequencyAsymptoticDimension_bound_and_eq
import Theorems.Thm_Eden_frequencyAsymptoticDimension_isGreatest
import Theorems.Thm_Eden_frequencyFiniteTimeDimension_bound_and_eq
import Theorems.Thm_Eden_frequencyFiniteTimeDimension_isGreatest
import Theorems.Thm_Eden_frequencyGlobalLyapunovDimension_attractor
import Theorems.Thm_Eden_tendsto_frequencyFiniteTimeDimension


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (ν : ℝ) :
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' attractor) (4+4/c) ∧
      ∀ p ∈ attractor, frequencyFiniteTimeDimension c ν t p = 4+4/c ↔ p ∈ torus) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' attractor) (4+4/c) ∧
    (∀ p ∈ attractor, frequencyAsymptoticDimension c ν p = 4+4/c ↔ p ∈ torus) ∧
    frequencyGlobalLyapunovDimension c ν attractor = 4+4/c ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => frequencyFiniteTimeDimension c ν t p) atTop
      (𝓝 (frequencyAsymptoticDimension c ν p))) :=
  ⟨fun t ht => ⟨frequencyFiniteTimeDimension_isGreatest hc ν ht,
      fun p hp => (frequencyFiniteTimeDimension_bound_and_eq hc ν ht hp).2⟩,
    frequencyAsymptoticDimension_isGreatest hc ν,
    fun p hp => (frequencyAsymptoticDimension_bound_and_eq hc ν hp).2,
    frequencyGlobalLyapunovDimension_attractor hc ν,
    fun p hp => tendsto_frequencyFiniteTimeDimension hc ν hp⟩
end EdenVerified
