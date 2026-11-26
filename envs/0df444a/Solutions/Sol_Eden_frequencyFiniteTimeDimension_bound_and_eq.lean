-- Prove2me | solution 1 for Eden.frequencyFiniteTimeDimension_bound_and_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:27.83592+00:00
-- url     : https://prove2.me/submissions/c0f43821-9453-4b02-8d29-b1182cb01e67

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_frequencyFiniteTimeDimension_eq
import Theorems.Thm_Eden_finiteTimeDimension_eq_target_iff
import Theorems.Thm_Eden_finiteTimeDimension_le_target


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c)
    (ν : ℝ) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) :
    frequencyFiniteTimeDimension c ν t p ≤ targetDimension c ∧
      (frequencyFiniteTimeDimension c ν t p = targetDimension c ↔ p ∈ torus) := by
  rw [frequencyFiniteTimeDimension_eq c ν ht.le]
  exact ⟨finiteTimeDimension_le_target hc ht hp, finiteTimeDimension_eq_target_iff hc ht hp⟩
end Eden
