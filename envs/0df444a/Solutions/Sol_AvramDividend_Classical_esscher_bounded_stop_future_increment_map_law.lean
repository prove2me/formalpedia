-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_future_increment_map_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:20:06.920904+00:00
-- url     : https://prove2.me/submissions/9f07fbaf-3c94-4a51-b857-29aa11ca00da

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_dyadic_grid_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_constant_restricted_real_law_pointwise_limit
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

/-- Bounded genuinely stopped increments have stationary tilted law under
one deterministic finite-terminal Esscher probability. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT.restrict A) = QT A • Measure.map (X.X u) QU := by
  intro QT QU
  have hQT : IsProbabilityMeasure QT :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  have hQU : IsProbabilityMeasure QU :=
    chat04_esscher_weighted_finite_horizon_probability X u θ hθ
  have hXu : Measurable (X.X u) := (X.adapted u).mono (𝓕.le u) le_rfl
  have hAm : MeasurableSet A := by
    have h1 : A = A ∩ {ω : Ω | τ ω ≤ H} := by
      ext ω; simp [hbound ω]
    rw [h1]; exact 𝓕.le H _ (hA H)
  obtain ⟨hgrid, hfib, hgridH, -, -, hlim⟩ :=
    bounded_stop_explicit_grid_increment_limit_with_horizon X τ hstop H hbound u
  have hstopn : ∀ n, IsStoppingTime 𝓕 (fun ω =>
      (((Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : WithTop ℝ≥0)) :=
    fun n => finite_grid_adapted_fibres_isStoppingTime _ _ (hgrid n) (hfib n)
  have hYn : ∀ n, Measurable (fun ω =>
      X.X ((Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n + u) ω -
        X.X ((Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω) := by
    intro n
    exact (measurable_pi_apply u).comp
      (levy_boundedStopping_stoppedFuturePath_measurable X _ (hstopn n) (H + 1)
        (fun ω => hgridH n _ (hgrid n ω)))
  have hY : Measurable (fun ω => X.X (τ ω + u) ω - X.X (τ ω) ω) :=
    (measurable_pi_apply u).comp
      (levy_boundedStopping_stoppedFuturePath_measurable X τ hstop H hbound)
  refine constant_restricted_real_law_pointwise_limit QT A hAm _ _ hYn hY hlim _ ?_
  intro n
  ext B hB
  rw [Measure.map_apply (hYn n) hB, Measure.restrict_apply (hYn n hB), Measure.smul_apply,
    Measure.map_apply hXu hB, smul_eq_mul, Set.inter_comm]
  exact esscher_bounded_stop_dyadic_grid_cylinder_factor X θ hθ τ hstop H hbound u T hT A hA n B hB


