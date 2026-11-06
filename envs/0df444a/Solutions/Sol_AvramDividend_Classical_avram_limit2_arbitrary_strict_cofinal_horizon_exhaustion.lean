-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:09:37.908809+00:00
-- url     : https://prove2.me/submissions/9078b43b-76f6-4884-b3ea-4b66b9b67158

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Any strictly cofinal deterministic real open-horizon family exhausts
    original perpetual cash and eventually includes each right-end atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a < T k) :
    dividendValue X q x D =
      ⨆ k : ℕ,
        ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T k),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P := by
  classical
  let closed : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P
  let strict : ℕ → ℝ≥0∞ := fun k =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T k),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P
  have hClosed (n : ℕ) : closed n ≤ ⨆ k : ℕ, strict k := by
    obtain ⟨k, hk⟩ := hT (n : ℝ)
    have hIncl : closed n ≤ strict k := by
      dsimp [closed, strict]
      apply lintegral_mono
      intro ω
      apply lintegral_mono_set
      intro t ht
      exact ⟨ht.1, lt_of_le_of_lt ht.2 hk⟩
    exact hIncl.trans (le_iSup strict k)
  have hStrict (k : ℕ) : strict k ≤ ⨆ n : ℕ, closed n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (T k)
    have hIncl : strict k ≤ closed n := by
      dsimp [strict, closed]
      apply lintegral_mono
      intro ω
      apply lintegral_mono_set
      intro t ht
      exact ⟨ht.1, le_of_lt (lt_trans ht.2 hn)⟩
    exact hIncl.trans (le_iSup closed n)
  rw [dividendValue_eq_iSup_truncated X q x D hD]
  change (⨆ n : ℕ, closed n) = ⨆ k : ℕ, strict k
  exact le_antisymm (iSup_le hClosed) (iSup_le hStrict)
