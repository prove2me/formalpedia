-- Prove2me | solution 1 for AvramDividend.Classical.esscher_terminal_future_increment_indep_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:18:09.464239+00:00
-- url     : https://prove2.me/submissions/9c313967-55e8-48f9-b8fe-bf8577c28179

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_map_law
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

/-- Under every deterministic terminal Esscher law, a future increment is independent of
the full earlier sigma-algebra, in Mathlib's genuine independence interface. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    ProbabilityTheory.Indep (𝓕 s)
      (MeasurableSpace.comap
        (fun ω : Ω => X.X (s + u) ω - X.X s ω)
        (inferInstance : MeasurableSpace ℝ))
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by
  let Y : Ω → ℝ := fun ω => X.X (s + u) ω - X.X s ω
  have hst : s ≤ s + u :=
    le_add_of_nonneg_right (show 0 ≤ u from zero_le)
  have hsT : s ≤ T := le_trans hst hT
  have hY : Measurable Y :=
    ((X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl).sub
      ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  apply (ProbabilityTheory.Indep_iff _ _ _).2
  intro A B hA hB
  change ∃ C : Set ℝ, MeasurableSet C ∧ Y ⁻¹' C = B at hB
  rcases hB with ⟨C, hC, rfl⟩
  have hPrefix :
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A :=
    (chat04_esscher_finite_horizon_laws_consistent_on_past_events
      X θ hθ s T hsT A hA).symm
  have hMap :
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) (Y ⁻¹' C) =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) ((X.X u) ⁻¹' C) := by
    have hh := congrArg (fun ν : Measure ℝ => ν C)
      (esscher_terminal_increment_map_law X θ hθ s u T hT)
    rw [Measure.map_apply hY hC, Measure.map_apply hXu hC] at hh
    exact hh
  calc
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ Y ⁻¹' C) =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) ((X.X u) ⁻¹' C) :=
        esscher_terminal_increment_cylinder_factorization
          X θ hθ s u T hT A hA C hC
    _ = _ := by rw [hPrefix, hMap]
