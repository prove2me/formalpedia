-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:40:00.987209+00:00
-- url     : https://prove2.me/submissions/d1fa5679-ef43-4dde-a91e-fd7c3f3cfda0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      (∀ (w : ℝ → ℝ) (f : ℝ → ℝ≥0∞),
        (∫⁻ s in Ioi (0 : ℝ),
          f s * ENNReal.ofReal
            (deriv w (riskProcess X x D s.toNNReal ω)) ∂μdiffuse) =
        (∫⁻ s in Ioi (0 : ℝ),
          f s * ENNReal.ofReal
            (deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse)) := by
  obtain ⟨A, μatom, μdiffuse, hcount, hmeas, hsplit,
      hatom, houtside, hnull, hmasses, htotal, hpre⟩ :=
    avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae
      X x D hD ω T
  refine ⟨A, μatom, μdiffuse, hcount, hmeas, hsplit,
    hatom, houtside, hnull, hmasses, htotal, ?_⟩
  intro w f
  apply setLIntegral_congr_fun_ae measurableSet_Ioi
  filter_upwards [hpre] with s hs hs0
  rw [hs hs0]
