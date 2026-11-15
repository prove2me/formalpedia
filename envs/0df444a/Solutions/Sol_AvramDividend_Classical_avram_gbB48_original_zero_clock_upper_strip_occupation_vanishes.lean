-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB48_original_zero_clock_upper_strip_occupation_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:10:27.846209+00:00
-- url     : https://prove2.me/submissions/221ede0f-c662-4dcb-805b-42ea1814b82c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x b : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (ρ : Ω → ℝ≥0) (ω : Ω) (hρ0 : ρ ω = 0) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) = 0 := by
  have hMeas : MeasurableSet (Ioo (0 : ℝ) (n : ℝ)) :=
    measurableSet_Ioo
  have hEq :
      (fun t : ℝ =>
        if t < (ρ ω : ℝ) ∧
            b < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0) =ᵐ[volume.restrict (Ioo 0 (n : ℝ))]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem hMeas] with t ht
    have hNot : ¬ t < (ρ ω : ℝ) := by
      rw [hρ0]
      exact not_lt.mpr (le_of_lt ht.1)
    simp [hNot]
  calc
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) =
        (∫ t in Ioo (0 : ℝ) (n : ℝ), (0 : ℝ) ∂volume) := by
          exact integral_congr_ae hEq
    _ = 0 := by simp
