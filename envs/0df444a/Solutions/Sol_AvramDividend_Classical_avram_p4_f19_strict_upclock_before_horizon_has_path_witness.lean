-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f19_strict_upclock_before_horizon_has_path_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:35:37.23457+00:00
-- url     : https://prove2.me/submissions/6f66c67c-5982-4a28-b79f-ca121b64906a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A strict finite-horizon upcrossing clock admits a pathwise upcrossing witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (z : ℝ) (ε : ℝ≥0) (ω : Ω)
    (hτ : twoSidedExitUpTimeCorrected X z ω < (ε : ℝ≥0∞)) :
    ∃ t : ℝ≥0, t < ε ∧ z < X.X t ω := by
  classical
  by_contra h
  push_neg at h
  have hpoint (t : ℝ≥0) (ht : z < X.X t ω) :
      (ε : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
    have hle : ε ≤ t := le_of_not_gt (fun hlt => (not_lt_of_ge (h t hlt)) ht)
    exact_mod_cast hle
  have hclock : (ε : ℝ≥0∞) ≤ twoSidedExitUpTimeCorrected X z ω := by
    unfold twoSidedExitUpTimeCorrected
    exact le_iInf fun t => le_iInf fun ht => hpoint t ht
  exact (not_lt_of_ge hclock) hτ
