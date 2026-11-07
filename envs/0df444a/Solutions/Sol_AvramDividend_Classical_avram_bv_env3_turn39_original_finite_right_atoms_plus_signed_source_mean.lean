-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn39_original_finite_right_atoms_plus_signed_source_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:50:31.753584+00:00
-- url     : https://prove2.me/submissions/09ae06b5-e9b6-49b1-adc9-3aa631c2bec4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Expected nonpositive signed original source remains nonpositive after
    adding all finite marked time-zero and strictly pre-ruin dividend atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (F : Ω → Finset ℝ≥0)
    (hF : ∀ ω t, t ∈ F ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (A : Ω → ℝ) (hAI : Integrable A P)
    (hAMean : (∫ ω, A ω ∂P) ≤ 0)
    (hAtomInt : Integrable (fun ω =>
      ∑ t ∈ F ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω))) P) :
    Integrable (fun ω => A ω +
      (∑ t ∈ F ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω)))) P ∧
    (∫ ω, A ω +
      (∑ t ∈ F ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω))) ∂P) ≤ 0 := by
  let R : Ω → ℝ := fun ω =>
    ∑ t ∈ F ω, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))
  have hR (ω : Ω) : R ω ≤ 0 := by
    dsimp [R]
    apply Finset.sum_nonpos
    intro t ht
    have hAtom := hjump ω t (hF ω t ht)
    have hSigned : (rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω) ≤ 0 := by
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hSigned
  have hRI : Integrable R P := hAtomInt
  have hRMean : (∫ ω, R ω ∂P) ≤ 0 := by
    apply integral_nonpos
    intro ω
    exact hR ω
  change Integrable (fun ω => A ω + R ω) P ∧
    (∫ ω, A ω + R ω ∂P) ≤ 0
  constructor
  · exact hAI.add hRI
  · rw [integral_add hAI hRI]
    exact add_nonpos hAMean hRMean
