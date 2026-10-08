-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_laplace_on_past_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:33:14.23204+00:00
-- url     : https://prove2.me/submissions/7e076314-e517-4399-aadb-09b8dca5ca40

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_condExp_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s h : ℝ≥0) (B : Set Ω) (hB : MeasurableSet[𝓕 s] B)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω in B,
      Real.exp (θ * (X.X (s + h) ω - X.X s ω)) ∂P =
        (P B).toReal * Real.exp ((h : ℝ) * X.ψ θ) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hs : s ≤ s + h :=
    le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ h by positivity)
  let F : Ω → ℝ := fun ω =>
    Real.exp (θ * (X.X (s + h) ω - X.X s ω) -
      (((s + h) - s : ℝ≥0) : ℝ) * X.ψ θ)
  have hInt : Integrable F P := by
    exact levy_compensated_future_increment_integrable X s (s + h) hs θ hθ
  have hCE : P[F | 𝓕 s] =ᵐ[P] (fun _ => (1 : ℝ)) := by
    exact levy_compensated_future_increment_condExp_one X s (s + h) hs θ hθ
  have hmB : MeasurableSet B := (𝓕.le s) B hB
  have hCEInt :
      (∫ ω in B, P[F | 𝓕 s] ω ∂P) =
      (∫ ω in B, (1 : ℝ) ∂P) := by
    apply setIntegral_congr_ae hmB
    filter_upwards [hCE] with ω heq
    intro _
    exact heq
  have hnorm : (∫ ω in B, F ω ∂P) = (P B).toReal := by
    calc
      (∫ ω in B, F ω ∂P) =
          ∫ ω in B, P[F | 𝓕 s] ω ∂P :=
        (setIntegral_condExp (𝓕.le s) hInt hB).symm
      _ = ∫ ω in B, (1 : ℝ) ∂P := hCEInt
      _ = (P B).toReal := by
        simp [measureReal_def]
  let K : ℝ := Real.exp ((((s + h) - s : ℝ≥0) : ℝ) * X.ψ θ)
  have hG :
      (fun ω => Real.exp (θ * (X.X (s + h) ω - X.X s ω))) =
        (fun ω => K * F ω) := by
    funext ω
    dsimp [K, F]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hG, integral_const_mul, hnorm]
  have htime : (s + h) - s = h := add_tsub_cancel_left s h
  dsimp [K]
  rw [htime]
  ring
