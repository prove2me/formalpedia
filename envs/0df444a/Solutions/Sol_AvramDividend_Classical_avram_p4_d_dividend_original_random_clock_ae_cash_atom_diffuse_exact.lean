-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_cash_atom_diffuse_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:54:23.410194+00:00
-- url     : https://prove2.me/submissions/48f89cfb-2b05-4c70-a05d-88fac60744df

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact original Cash atom/diffuse decomposition survives a path-dependent
    finite stop, including zero-time and eligible horizon right-payment atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (τ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      let μ : Measure ℝ :=
        (dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ))
      let f : ℝ → ℝ≥0∞ := fun s =>
        if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0
      ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
        A.Countable ∧ MeasurableSet A ∧
        μ = μatom + μdiffuse ∧
        NullSingletonClass μdiffuse ∧
        μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
        μ Set.univ = ENNReal.ofReal (rightLimit D (τ ω) ω) ∧
        (∀ t : ℝ≥0, t ≤ τ ω →
          μatom {(t : ℝ)} =
            ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
        ((∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
            (∑' a : A, f a.1 * μatom {a.1}).toReal +
            (∫⁻ s : ℝ, f s ∂μdiffuse).toReal) := by
  apply Filter.Eventually.of_forall
  intro ω
  exact avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
    X x D hD q hq ω (τ ω)