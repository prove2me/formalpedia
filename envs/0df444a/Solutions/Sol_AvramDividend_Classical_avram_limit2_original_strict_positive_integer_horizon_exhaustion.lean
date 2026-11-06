-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_strict_positive_integer_horizon_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:18:28.680115+00:00
-- url     : https://prove2.me/submissions/ac63e730-3beb-430c-a6c3-9424f3e32cb2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict positive integer horizons exhaust the original closed-ruin
    dividend value, retaining the time-zero atom and every finite endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    dividendValue X q x D =
      ⨆ n : ℕ,
        ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iio (((n + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P := by
  classical
  let cashClosed : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P
  let cashStrict : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iio (((n + 1 : ℕ) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P
  have hClosed_le_strict (n : ℕ) : cashClosed n ≤ cashStrict n := by
    dsimp [cashClosed, cashStrict]
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    have hn : (n : ℝ) < (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.lt_succ_self n
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hn⟩
  have hStrict_le_closed (n : ℕ) : cashStrict n ≤ cashClosed (n + 1) := by
    dsimp [cashStrict, cashClosed]
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    refine ⟨ht.1, ?_⟩
    change t ≤ (((n + 1 : ℕ) : ℝ))
    exact le_of_lt ht.2
  have hExhaust := dividendValue_eq_iSup_truncated X q x D hD
  change dividendValue X q x D = ⨆ n : ℕ, cashStrict n
  rw [hExhaust]
  change (⨆ n : ℕ, cashClosed n) = ⨆ n : ℕ, cashStrict n
  apply le_antisymm
  · exact iSup_le fun n =>
      (hClosed_le_strict n).trans (le_iSup cashStrict n)
  · exact iSup_le fun n =>
      (hStrict_le_closed n).trans (le_iSup cashClosed (n + 1))
