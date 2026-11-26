-- Prove2me | solution 1 for Eden.tendsto_frequencyFiniteTimeDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:02.142503+00:00
-- url     : https://prove2.me/submissions/1ae603c4-e1cc-4d25-b4b8-bfadb7f0b77c

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_frequencyFiniteTimeDimension_eq
import Theorems.Thm_Eden_frequencyAsymptoticDimension_eq
import Theorems.Thm_Eden_tendsto_finiteTimeDimension


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (ν : ℝ)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    Tendsto (fun t : ℝ => frequencyFiniteTimeDimension c ν t p) atTop
      (𝓝 (frequencyAsymptoticDimension c ν p)) := by
  rw [frequencyAsymptoticDimension_eq]
  apply (tendsto_finiteTimeDimension hc hp).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (frequencyFiniteTimeDimension_eq c ν ht p).symm
end Eden
