-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_strict_uniform_event_expected_reward_from_source_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:11:20.530831+00:00
-- url     : https://prove2.me/submissions/980a265e-d9b7-4e17-96a0-5def7eb8c5d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_preruin_uniform_caplinear_full_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (t : ℝ≥0) (m : ℕ) (A : Set Ω)
    (hA : MeasurableSet A)
    (hSurvive : ∀ ω ∈ A, (t : ℝ≥0∞) < ruinTime X x D ω)
    (Reward Source : Ω → ℝ)
    (hReward : ∀ ω, Reward ω =
      let u : ℕ → ℝ≥0 := fun i =>
        min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * t) t
      Real.exp (-(q * (u (m + 1) : ℝ))) *
        V (x + X.X (u (m + 1)) ω - rightLimit D (u (m + 1)) ω) +
      (∫⁻ s in Icc (0 : ℝ) (u (m + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hSource : ∀ ω, Source ω =
      let u : ℕ → ℝ≥0 := fun i =>
        min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * t) t
      let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
      let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
          E (u i) * (V (Z i) - V (Y (u i)))))
    (hRewardI : Integrable Reward (P.restrict A))
    (hSourceI : Integrable Source (P.restrict A))
    (hMeanSource : (∫ ω in A, Source ω ∂P) ≤ 0) :
    (∫ ω in A, Reward ω ∂P) ≤ V x * (P A).toReal := by 
  have hPoint : ∀ ω ∈ A, Reward ω ≤ V x + Source ω := by
    intro ω hω
    rw [hReward ω, hSource ω]
    exact avram_pj_workerC_true_preruin_uniform_caplinear_full_cash
      X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω t (hSurvive ω hω) m
  have hAE : ∀ᵐ ω ∂(P.restrict A), Reward ω ≤ V x + Source ω := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    exact hPoint ω hω
  have hSumI : Integrable (fun ω => V x + Source ω) (P.restrict A) :=
    (integrable_const (V x)).add hSourceI
  have hUpper := integral_mono_ae hRewardI hSumI hAE
  have hAdd :
      (∫ ω in A, V x + Source ω ∂P) =
        V x * (P A).toReal + (∫ ω in A, Source ω ∂P) := by
    rw [integral_add (integrable_const (V x)) hSourceI]
    simpa [Measure.real, mul_comm]
  calc
    (∫ ω in A, Reward ω ∂P) ≤
        (∫ ω in A, V x + Source ω ∂P) := hUpper
    _ = V x * (P A).toReal + (∫ ω in A, Source ω ∂P) := hAdd
    _ ≤ V x * (P A).toReal := by linarith
