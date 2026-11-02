-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_diffuse_real_integral_strictpre_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:53:31.582662+00:00
-- url     : https://prove2.me/submissions/730bbc4c-6a5a-4bda-9d8d-6420e5fd5c8c

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

/-- The genuine atomless dividend Stieltjes real signed derivative integral
is unchanged by replacing the controlled reserve with the strict original
Lévy source-prejump, dividend-right-limit reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
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
      (∀ (w : ℝ → ℝ) (q : ℝ),
        (∫ s in Ioi (0 : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂μdiffuse) =
        (∫ s in Ioi (0 : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse)) := by
  rcases avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae
    X x D hD.1 ω T with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
      hOutside, hNull, hAt, _hMass, hPreEq⟩
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
    hAtom, hOutside, hNull, hAt, ?_⟩
  intro w q
  apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
  filter_upwards [hPreEq] with s hs hs0
  rw [hs hs0]
