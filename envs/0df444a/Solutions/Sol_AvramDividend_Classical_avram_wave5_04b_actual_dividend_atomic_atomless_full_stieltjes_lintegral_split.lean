-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:45:57.7025+00:00
-- url     : https://prove2.me/submissions/4cd05587-2640-475c-8877-da0c7ba884c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every weighted complete dividend Stieltjes lower integral splits exactly into its countably right-atomic component (including time zero) and its atomless component, which retains all diffuse and singular-continuous variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
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
      (∫⁻ s, f s ∂μ) =
        (∫⁻ s, f s ∂μatom) + (∫⁻ s, f s ∂μdiffuse) := by
  rcases avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq
    X x D hD ω T with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hEq, hAtom, hSupp,
      hNull, hAt, hMass, hDiffEq⟩
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hEq, hAtom,
    hSupp, hNull, hAt, ?_⟩
  rw [hEq]
  exact MeasureTheory.lintegral_add_measure f μatom μdiffuse
