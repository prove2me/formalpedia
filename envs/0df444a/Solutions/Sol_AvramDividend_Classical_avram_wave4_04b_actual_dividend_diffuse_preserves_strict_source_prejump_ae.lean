-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:16:42.762205+00:00
-- url     : https://prove2.me/submissions/f508d58b-ef28-4b58-9c1d-51833a4de576

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure

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
      (∀ᵐ s ∂μdiffuse, 0 < s →
        riskProcess X x D s.toNNReal ω =
          x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) := by
  dsimp only
  rcases avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
      D hD ω T with
    ⟨A, μatom, μdiffuse, hAc, hAm, hdecomp, hatom, hsupport,
      hnull, hsingle, htotal⟩
  letI : NullSingletonClass μdiffuse := hnull
  refine ⟨A, μatom, μdiffuse, hAc, hAm, hdecomp, hatom,
    hsupport, hnull, hsingle, htotal, ?_⟩
  exact avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
    X x D hD ω μdiffuse
