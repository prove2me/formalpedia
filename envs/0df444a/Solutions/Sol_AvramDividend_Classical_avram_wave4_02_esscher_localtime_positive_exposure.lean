-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_localtime_positive_exposure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:24:19.50953+00:00
-- url     : https://prove2.me/submissions/16d3d1af-9ea7-44f8-845d-bf33aa160f60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_true_localtime_positive_mass
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_null_events_iff
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual finite-horizon Esscher law gives positive expected exposure
to the source running-supremum local-time normalisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 < ∫⁻ ω, ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω)
      ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp
          (φ * X.X (1 : ℝ≥0) ω - (1 : ℝ) * X.ψ φ)))) := by
  let Q : Measure Ω := P.withDensity (fun ω : Ω =>
    ENNReal.ofReal (Real.exp
      (φ * X.X (1 : ℝ≥0) ω - (1 : ℝ) * X.ψ φ)))
  have hP : 0 < P {ω : Ω | 0 < runningSup X (1 : ℝ≥0) ω} :=
    avram_wave4_02_true_localtime_positive_mass X q hq φ hφ hroot
  have hQ : 0 < Q {ω : Ω | 0 < runningSup X (1 : ℝ≥0) ω} := by
    by_contra hNotPositive
    have hZero : Q {ω : Ω | 0 < runningSup X (1 : ℝ≥0) ω} = 0 :=
      bot_unique (not_lt.mp hNotPositive)
    have hZeroP : P {ω : Ω | 0 < runningSup X (1 : ℝ≥0) ω} = 0 :=
      (chat04_esscher_finite_horizon_null_events_iff X 1 φ _).mp hZero
    exact (ne_of_gt hP) hZeroP
  have hMeas : Measurable (fun ω : Ω => runningSup X (1 : ℝ≥0) ω) := by
    exact (levy_runningSup_joint_time_path_measurable X).comp
      (measurable_const.prodMk measurable_id)
  have hOfRealMeas : Measurable
      (fun ω : Ω => ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω)) :=
    hMeas.ennreal_ofReal
  have hSupport :
      0 < Q (Function.support
        (fun ω : Ω => ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω))) := by
    apply lt_of_lt_of_le hQ
    apply measure_mono
    intro ω hw
    change ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hw)
  change 0 < ∫⁻ ω, ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω) ∂Q
  exact (lintegral_pos_iff_support hOfRealMeas).2 hSupport
