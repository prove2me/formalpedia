-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:35:51.641204+00:00
-- url     : https://prove2.me/submissions/6435b1eb-b3cc-450a-b86e-23e3473d5cf5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The actual stopped signed dividend term includes the time-zero atom
    even when ruin is immediate; for positive times it requires τ < σ. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
       V (x + X.X (τ ω) ω)) ≤ 0 := by
  have hDomain :
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
        Icc (0 : ℝ) (τ ω : ℝ) := by
    rcases hPre with hzero | hStrict
    · rw [hzero]
      ext t
      constructor
      · intro ht
        exact ⟨ht.1.1, ht.2⟩
      · intro ht
        exact ⟨⟨ht.1, Or.inl (le_antisymm ht.2 ht.1)⟩, ht.2⟩
    · exact avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
        X x D ω τ hStrict
  have hSigned :=
    avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
      X x C q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω (τ ω) hPre
  simpa only [hDomain] using hSigned
