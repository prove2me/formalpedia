-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:34:39.318389+00:00
-- url     : https://prove2.me/submissions/cc18f5a6-4df3-4264-a4f8-4978d7a8a262

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! One original probability-one event supports eventual exact payment
    domains at every horizon in a countable nonnegative real family. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (horizons : ℕ → ℝ)
    (hT : ∀ k : ℕ, 0 ≤ horizons k) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩
        Iic (horizons k) =
      paymentTimes (ruinTime X x D ω) ∩ Iic (horizons k) := by
  rw [ae_all_iff]
  intro k
  exact avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises
    X hBV x C D hD (horizons k) (hT k) S hSliminfAE
end
