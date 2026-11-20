-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_random_precontact_original_expected_reward_from_spatial_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:22:25.054181+00:00
-- url     : https://prove2.me/submissions/c0724a47-da41-40b3-a363-8fa6e45315df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_preruin_original_cash_le_nonlinear_spatial_gain
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0) (m : ℕ) (A : Set Ω)
    (hA : MeasurableSet A)
    (hSurvive : ∀ ω ∈ A, (ρ ω : ℝ≥0∞) < ruinTime X x D ω)
    (Reward Source : Ω → ℝ)
    (hReward : ∀ ω, Reward ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω) +
      (∫⁻ s in Icc (0 : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hSource : ∀ ω, Source ω =
      let u : ℕ → ℝ≥0 := fun i =>
        min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * ρ ω) (ρ ω)
      let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
      let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      ∑ i ∈ Finset.range (m + 1),
        E (u i) * (V (Z i) - V (Y (u i))))
    (hRewardI : Integrable Reward (P.restrict A))
    (hSourceI : Integrable Source (P.restrict A))
    (ε : ℝ) (hMeanSource : (∫ ω in A, Source ω ∂P) ≤ ε) :
    (∫ ω in A, Reward ω ∂P) ≤ w x * (P A).toReal + ε := by 
  have hPoint : ∀ ω ∈ A, Reward ω ≤ w x + Source ω := by
    intro ω hω
    rw [hReward ω, hSource ω]
    exact avram_pj_workerC_preruin_original_cash_le_nonlinear_spatial_gain
      X x C hC hx hxc q hq w V hw0 hw_cont hw_neg
      hw_smooth hw_grad hVtop hVfinite D hD
      ω (ρ ω) (hSurvive ω hω) m
  have hAE : ∀ᵐ ω ∂(P.restrict A), Reward ω ≤ w x + Source ω := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    exact hPoint ω hω
  have hSumI : Integrable (fun ω => w x + Source ω) (P.restrict A) :=
    (integrable_const (w x)).add hSourceI
  have hUpper := integral_mono_ae hRewardI hSumI hAE
  have hAdd :
      (∫ ω in A, w x + Source ω ∂P) =
        w x * (P A).toReal + (∫ ω in A, Source ω ∂P) := by
    rw [integral_add (integrable_const (w x)) hSourceI]
    simpa [Measure.real, mul_comm]
  calc
    (∫ ω in A, Reward ω ∂P) ≤
        (∫ ω in A, w x + Source ω ∂P) := hUpper
    _ = w x * (P A).toReal + (∫ ω in A, Source ω ∂P) := hAdd
    _ ≤ w x * (P A).toReal + ε := by linarith
