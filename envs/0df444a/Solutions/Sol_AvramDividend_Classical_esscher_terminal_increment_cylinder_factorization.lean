-- Prove2me | solution 1 for AvramDividend.Classical.esscher_terminal_increment_cylinder_factorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:15:49.514354+00:00
-- url     : https://prove2.me/submissions/188c86bd-b975-4c20-a1d5-2a3a0f718612

import Theorems.Thm_AvramDividend_Classical_esscher_adjacent_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Under any later Esscher terminal law the past and adjacent future increment factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  have hst : s ≤ s + u :=
    le_add_of_nonneg_right (show 0 ≤ u from zero_le)
  have hY : Measurable[𝓕 (s + u)]
      (fun ω : Ω => X.X (s + u) ω - X.X s ω) :=
    (X.adapted (s + u)).sub
      ((X.adapted s).mono (𝓕.mono hst) le_rfl)
  have hE : @MeasurableSet Ω (𝓕 (s + u))
      (A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) :=
    ((𝓕.mono hst) A hA).inter (hY hB)
  calc
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
        (A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (s + u) ω -
          (s + u : ℝ) * X.ψ θ))))
        (A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) := by
          exact (chat04_esscher_finite_horizon_laws_consistent_on_past_events
            X θ hθ (s + u) T hT _ hE).symm
    _ = _ :=
      esscher_adjacent_increment_cylinder_factorization
        X θ hθ s u A hA B hB
