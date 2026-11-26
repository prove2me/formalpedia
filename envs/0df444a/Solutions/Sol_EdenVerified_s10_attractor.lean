-- Prove2me | solution 1 for EdenVerified.s10_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:23.111678+00:00
-- url     : https://prove2.me/submissions/66abac70-585e-4de3-89c1-f16ae0d467c4

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_attractor_isFrequencyGlobalAttractor
import Theorems.Thm_Eden_frequencyEvolution_mem_torus
import Theorems.Thm_Eden_frequency_attractor_minimal


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (ν : ℝ) :
    IsFrequencyGlobalAttractor c ν attractor ∧
    (∀ t : ℝ, ∀ p ∈ torus, frequencyEvolution c ν t p ∈ torus) ∧
    (∀ C : Set PhaseSpace, IsClosed C →
      FrequencyUniformlyAttractsBounded c ν C → attractor ⊆ C) :=
  ⟨attractor_isFrequencyGlobalAttractor (by linarith) ν,
    fun t p hp => frequencyEvolution_mem_torus c ν t hp,
    fun C hC hA => frequency_attractor_minimal hC hA⟩
end EdenVerified
