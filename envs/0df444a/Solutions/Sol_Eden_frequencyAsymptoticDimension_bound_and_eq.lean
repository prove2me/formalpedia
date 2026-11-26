-- Prove2me | solution 1 for Eden.frequencyAsymptoticDimension_bound_and_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:24.135801+00:00
-- url     : https://prove2.me/submissions/70881e16-8b95-4d99-88f8-a7c1b71ddfbe

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_frequencyAsymptoticDimension_eq
import Theorems.Thm_Eden_asymptoticDimension_eq_target_iff
import Theorems.Thm_Eden_asymptoticDimension_le_target


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    (ν : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    frequencyAsymptoticDimension c ν p ≤ targetDimension c ∧
      (frequencyAsymptoticDimension c ν p = targetDimension c ↔ p ∈ torus) := by
  rw [frequencyAsymptoticDimension_eq]
  exact ⟨asymptoticDimension_le_target hc p, asymptoticDimension_eq_target_iff hc hp⟩
end Eden
