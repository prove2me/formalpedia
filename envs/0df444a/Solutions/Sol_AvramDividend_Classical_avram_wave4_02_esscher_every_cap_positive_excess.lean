-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_every_cap_positive_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:22:01.55581+00:00
-- url     : https://prove2.me/submissions/88dd644c-fef9-4e90-81f2-cc790f5b3bdc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_localtime_every_cap_positive
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_null_events_iff
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine finite Esscher laws put strictly positive expected local-time
excess above every deterministic cap at every positive finite time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (t : ℝ≥0) (ht : 0 < t) (b θ : ℝ) :
    0 < ∫⁻ ω, ENNReal.ofReal (runningSup X t ω - b)
      ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp
          (θ * X.X t ω - (t : ℝ) * X.ψ θ)))) := by
  let Q : Measure Ω := P.withDensity (fun ω : Ω =>
    ENNReal.ofReal (Real.exp
      (θ * X.X t ω - (t : ℝ) * X.ψ θ)))
  have hP : 0 < P {ω : Ω | b < runningSup X t ω} :=
    avram_wave4_02_source_localtime_every_cap_positive X hvar t ht b
  have hQ : 0 < Q {ω : Ω | b < runningSup X t ω} := by
    by_contra hNotPositive
    have hZero : Q {ω : Ω | b < runningSup X t ω} = 0 :=
      bot_unique (not_lt.mp hNotPositive)
    have hZeroP : P {ω : Ω | b < runningSup X t ω} = 0 :=
      (chat04_esscher_finite_horizon_null_events_iff X t θ _).mp hZero
    exact (ne_of_gt hP) hZeroP
  have hMeas : Measurable (fun ω : Ω => runningSup X t ω) := by
    exact (levy_runningSup_joint_time_path_measurable X).comp
      (measurable_const.prodMk measurable_id)
  have hOfRealMeas : Measurable
      (fun ω : Ω => ENNReal.ofReal (runningSup X t ω - b)) :=
    (hMeas.sub measurable_const).ennreal_ofReal
  have hSupport :
      0 < Q (Function.support
        (fun ω : Ω => ENNReal.ofReal (runningSup X t ω - b))) := by
    apply lt_of_lt_of_le hQ
    apply measure_mono
    intro ω hw
    change ENNReal.ofReal (runningSup X t ω - b) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hw))
  change 0 < ∫⁻ ω, ENNReal.ofReal (runningSup X t ω - b) ∂Q
  exact (lintegral_pos_iff_support hOfRealMeas).2 hSupport
