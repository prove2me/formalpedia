-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_joint_regulator_reflection_projective_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:06:51.064287+00:00
-- url     : https://prove2.me/submissions/a598ca24-995c-4a01-b057-b33a5079835c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The *joint* actual record local-time and reflected drawdown at any fixed
horizon has the same distribution under later finite Esscher terminal laws. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (H T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁) (hT₂ : H + 1 ≤ T₂) :
    Measure.map (fun ω : Ω => (runningSup X H ω, reflectedSup X H ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₁ ω - (T₁ : ℝ) * X.ψ φ)))) =
    Measure.map (fun ω : Ω => (runningSup X H ω, reflectedSup X H ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₂ ω - (T₂ : ℝ) * X.ψ φ)))) := by
  have hfun : barrierStrategy X 0 0 = fun t ω => runningSup X t ω := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  have hadapt : Adapted 𝓕 (fun t ω => runningSup X t ω) :=
    hfun ▸ barrierStrategy_adapted X 0
  let Y : Ω → ℝ × ℝ := fun ω =>
    (runningSup X H ω, reflectedSup X H ω)
  have hYfil : Measurable[𝓕 H] Y :=
    (hadapt H).prodMk (reflectedSup_adapted X H)
  have hY : Measurable Y := hYfil.mono (𝓕.le H) le_rfl
  have hstop : IsStoppingTime 𝓕
      (fun _ : Ω => (H : WithTop ℝ≥0)) := by
    intro s
    by_cases hs : H ≤ s
    · simp [hs]
    · simp [hs]
  have hYstop : ∀ A : Set (ℝ × ℝ), MeasurableSet A →
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
