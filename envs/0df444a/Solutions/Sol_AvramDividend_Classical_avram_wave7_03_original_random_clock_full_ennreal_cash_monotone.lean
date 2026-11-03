-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_random_clock_full_ennreal_cash_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:51:42.720196+00:00
-- url     : https://prove2.me/submissions/b5b7b110-b49a-43af-95d9-5b1ca5bfeac6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original outer cash monotonicity under ordered pathwise
    stopping clocks, including a possible atom at the later clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ σ : Ω → ℝ≥0)
    (hClock : ∀ ω, τ ω ≤ σ ω) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  apply MeasureTheory.lintegral_mono
  intro ω
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  have hLe : (τ ω : ℝ) ≤ (σ ω : ℝ) := by
    exact_mod_cast hClock ω
  exact ⟨ht.1, (Set.mem_Iic.mp ht.2).trans hLe⟩
