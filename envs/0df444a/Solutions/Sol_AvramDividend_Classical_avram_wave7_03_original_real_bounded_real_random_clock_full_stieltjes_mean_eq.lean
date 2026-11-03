-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_bounded_real_random_clock_full_stieltjes_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:34:41.79691+00:00
-- url     : https://prove2.me/submissions/664ecf8d-8d5b-40c5-a9ac-2449c733c53f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_real_random_clock_full_stieltjes_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Real deterministic upper bound and real measurable random clock for
    exact original ruin-stopped Stieltjes/ENNReal expected cash equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable τ) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hBoundNN : ∀ ω, τ ω ≤ (T.toNNReal : ℝ) := by
    intro ω
    rw [Real.coe_toNNReal T hT]
    exact hτBound ω
  exact avram_wave7_03_original_bounded_real_random_clock_full_stieltjes_mean_eq
    X x C D hD q hq T.toNNReal τ hτNonneg hBoundNN hτMeas
