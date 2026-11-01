-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_finite_truncated_localtime_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:40:28.194696+00:00
-- url     : https://prove2.me/submissions/fb0fac7a-0e82-4601-b157-d560d83e8360

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_localtime_positive_exposure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine time-one tilted path has a strictly positive and finite
capped running-supremum local-time normaliser for each positive cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (B : ℝ) (hB : 0 < B) :
    (let Q : Measure Ω :=
       P.withDensity (fun ω : Ω => ENNReal.ofReal
         (Real.exp (φ * X.X (1 : ℝ≥0) ω - (1 : ℝ) * X.ψ φ)))
     0 < ∫⁻ ω, ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B) ∂Q ∧
     (∫⁻ ω, ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B) ∂Q)
       ≤ ENNReal.ofReal B) := by
  let Q : Measure Ω := P.withDensity (fun ω : Ω =>
    ENNReal.ofReal (Real.exp
      (φ * X.X (1 : ℝ≥0) ω - (1 : ℝ) * X.ψ φ)))
  haveI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact chat04_esscher_weighted_finite_horizon_probability
      X 1 φ (le_of_lt hφ)
  have hMeas : Measurable (fun ω : Ω => runningSup X (1 : ℝ≥0) ω) := by
    exact (levy_runningSup_joint_time_path_measurable X).comp
      (measurable_const.prodMk measurable_id)
  have hMeasS : Measurable
      (fun ω : Ω => ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω)) :=
    hMeas.ennreal_ofReal
  have hMeasCap : Measurable
      (fun ω : Ω => ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B)) :=
    (hMeas.min measurable_const).ennreal_ofReal
  have hExpPos :
      0 < ∫⁻ ω, ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω) ∂Q := by
    exact avram_wave4_02_esscher_localtime_positive_exposure
      X q hq φ hφ hroot
  have hSupport :
      0 < Q (Function.support
        (fun ω : Ω => ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω))) :=
    (lintegral_pos_iff_support hMeasS).1 hExpPos
  have hSupportLe :
      Function.support
        (fun ω : Ω => ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω)) ⊆
      Function.support
        (fun ω : Ω => ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B)) := by
    intro ω hw
    have hs : 0 < runningSup X (1 : ℝ≥0) ω := by
      apply ENNReal.ofReal_pos.mp
      exact pos_iff_ne_zero.mpr hw
    change ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (lt_min hs hB))
  have hCapSupport :
      0 < Q (Function.support
        (fun ω : Ω => ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B))) :=
    lt_of_lt_of_le hSupport (measure_mono hSupportLe)
  change (0 < ∫⁻ ω, ENNReal.ofReal
      (min (runningSup X (1 : ℝ≥0) ω) B) ∂Q) ∧
    (∫⁻ ω, ENNReal.ofReal
      (min (runningSup X (1 : ℝ≥0) ω) B) ∂Q) ≤ ENNReal.ofReal B
  constructor
  · exact (lintegral_pos_iff_support hMeasCap).2 hCapSupport
  · calc
      (∫⁻ ω, ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B) ∂Q)
          ≤ ∫⁻ _ : Ω, ENNReal.ofReal B ∂Q := by
              apply lintegral_mono
              intro ω
              exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = ENNReal.ofReal B := by simp
