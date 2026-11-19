-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_positive_event_all_original_short_meshes_centered_noise_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:50:10.5361+00:00
-- url     : https://prove2.me/submissions/eada68aa-f07c-41fd-9d93-595847aadb39

import Mathlib.Tactic.NormNum
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem solution [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ ω ∈ E, ∀ m : ℕ, 15999 ≤ m →
          let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
          let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
          |(Finset.range (m + 1)).sum (fun i =>
            if s i < (1 / 1000 : ℝ≥0) then
              Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
                (Y.X (s (i + 1)) ω - Y.X (s i) ω -
                  ((s (i + 1) : ℝ) - (s i : ℝ)) * Y.c)
            else 0)| ≤ (1 / 4000 : ℝ) := by
  obtain ⟨𝓕, Y, hc, hσ, hν, hStanding, hBV, hAdm, E,
      hEMeas, hEPos, hTube⟩ :=
    avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
  refine ⟨𝓕, Y, hc, hσ, hν, hStanding, hBV,
    hAdm, E, hEMeas, hEPos, ?_⟩
  intro ω hω m hm
  have hSource (u : ℝ≥0) (hu : u ≤ (17 / 16000 : ℝ≥0)) :
      Y.X u ω = (brownian u ω - brownian 0 ω) + 2 * (u : ℝ) :=
    (hTube ω hω u hu).1
  have hCentered (u : ℝ≥0) (hu : u ≤ (17 / 16000 : ℝ≥0)) :
      |brownian u ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) :=
    (hTube ω hω u hu).2.1
  have hTime : (1 / 1000 : ℝ≥0) ≤ (17 / 16000 : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    norm_num [NNReal.coe_div]
  have hDrifted (u : ℝ≥0) (hu : u ≤ (1 / 1000 : ℝ≥0)) :
      |Y.X u ω| ≤ (1 / 400 : ℝ) :=
    (hTube ω hω u (le_trans hu hTime)).2.2
  have hResult :=
    avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
      Y ω (fun u ω => brownian u ω - brownian 0 ω)
      hSource hc (Y.X_zero ω) hCentered hDrifted m hm
  exact hResult.2.2
