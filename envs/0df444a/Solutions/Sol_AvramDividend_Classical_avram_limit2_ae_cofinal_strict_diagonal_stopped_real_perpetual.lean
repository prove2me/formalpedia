-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ae_cofinal_strict_diagonal_stopped_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:26:21.816196+00:00
-- url     : https://prove2.me/submissions/d37ca9db-44f1-4f0b-ae61-98014b78d804

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict positive diagonal horizons dominate closed ones, giving true
    perpetual original ruin-stopped real cash without losing finite atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞) (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hStrictDiag : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iio (((k + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
      ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hClosedDiag : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (k : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
      ≤ B + error k := by
    intro k
    have hk : (k : ℝ) < (((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.lt_succ_self k
    calc
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (k : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P) ≤
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iio (((k + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P) := by
          apply lintegral_mono
          intro ω
          apply add_le_add_left
          apply lintegral_mono_set
          intro t ht
          exact ⟨ht.1, lt_of_le_of_lt ht.2 hk⟩
      _ ≤ B + error k := hStrictDiag k
  exact avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual
    X q x D hD B hB σ hσmeas hσmono hSup
      Terminal error hError hClosedDiag
