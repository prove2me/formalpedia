-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_running_localtime_cap_projective_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:53:56.434647+00:00
-- url     : https://prove2.me/submissions/bed1048c-0305-4842-826e-d449d5ad68a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual source local-time regulator capped at B has exactly the same
whole distribution under any two later finite Esscher terminal horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (H T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁) (hT₂ : H + 1 ≤ T₂)
    (B : ℝ) (hB : 0 < B) :
    Measure.map (fun ω : Ω => min (runningSup X H ω) B)
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₁ ω - (T₁ : ℝ) * X.ψ φ)))) =
    Measure.map (fun ω : Ω => min (runningSup X H ω) B)
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₂ ω - (T₂ : ℝ) * X.ψ φ)))) := by
  have hfun : barrierStrategy X 0 0 = fun t ω => runningSup X t ω := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  have hadapt : Adapted 𝓕 (fun t ω => runningSup X t ω) :=
    hfun ▸ barrierStrategy_adapted X 0
  let Y : Ω → ℝ := fun ω => min (runningSup X H ω) B
  have hY : Measurable Y := by
    exact ((levy_runningSup_joint_time_path_measurable X).comp
      (measurable_const.prodMk measurable_id)).min measurable_const
  have hYfil : Measurable[𝓕 H] Y := (hadapt H).min measurable_const
  have hstop : IsStoppingTime 𝓕
      (fun _ : Ω => (H : WithTop ℝ≥0)) := by
    intro s
    by_cases hs : H ≤ s
    · simp [hs]
    · simp [hs]
  have hYstop : ∀ A : Set ℝ, MeasurableSet A →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' A) ∩ {ω : Ω | H ≤ s}) := by
    intro A hA s
    by_cases hs : H ≤ s
    · have hm : Measurable[𝓕 s] Y :=
        hYfil.mono (𝓕.mono hs) le_rfl
      simpa [hs] using hm hA
    · simp [hs]
  exact esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
    X φ (le_of_lt hφ) (fun _ : Ω => H) hstop
    H (fun _ => le_rfl) T₁ T₂ hT₁ hT₂ Y hY hYstop
