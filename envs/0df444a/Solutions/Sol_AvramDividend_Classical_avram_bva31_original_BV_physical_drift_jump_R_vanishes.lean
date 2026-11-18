-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva31_original_BV_physical_drift_jump_R_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:41:36.363204+00:00
-- url     : https://prove2.me/submissions/9792aae8-cfe2-43d7-8a62-8083b4b3588c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_BV_interval_physical_jump_drift_ledger
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0 := by
  filter_upwards [avram_bva22_original_BV_interval_physical_jump_drift_ledger X hX hBV]
    with ω hω
  intro t
  have h0t : (0 : ℝ≥0) ≤ t := by positivity
  have h := hω 0 t h0t
  have ht : X.X t ω = (t : ℝ) * X.drift -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0) := by
    simpa only [X.X_zero ω, sub_zero, NNReal.coe_zero, zero_mul] using h
  rw [ht]
  ring
