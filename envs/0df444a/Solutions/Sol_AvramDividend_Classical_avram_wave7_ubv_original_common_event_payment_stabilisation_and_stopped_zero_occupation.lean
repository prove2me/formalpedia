-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_common_event_payment_stabilisation_and_stopped_zero_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:48:36.84896+00:00
-- url     : https://prove2.me/submissions/f6d4731d-90c1-4508-889f-6cfb2d59fb3b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_countable_stopped_zero_occupation_variable_time_measures

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! A single original probability-one event combines exact eventual
    dividend domains and sigma-finite positivity for the SAME clocks. -/
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
    (hT : ∀ k : ℕ, 0 ≤ horizons k)
    (times radii : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < radii n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, radii n ≤ ε)
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ n, SFinite (μ n)) :
    ∀ᵐ ω ∂P,
      (∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩
          Iic (horizons k) =
        paymentTimes (ruinTime X x D ω) ∩ Iic (horizons k)) ∧
      (∀ n : ℕ, ∀ᵐ (t : ℝ≥0) ∂μ n,
        (t : ℝ≥0∞) < min (ruinTime X x D ω) (S n ω) →
          0 < riskProcess X x D t ω) := by
  have hdom :
      ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩
          Iic (horizons k) =
        paymentTimes (ruinTime X x D ω) ∩ Iic (horizons k) :=
    avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
      X hBV x C D hD S hSliminfAE horizons hT
  have hocc :
      ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ (t : ℝ≥0) ∂μ n,
        (t : ℝ≥0∞) < min (ruinTime X x D ω) (S n ω) →
          0 < riskProcess X x D t ω :=
    avram_wave7_ubv_original_countable_stopped_zero_occupation_variable_time_measures
      X hBV x C D hD
      (fun n ω => min (ruinTime X x D ω) (S n ω))
      (by intro n ω; exact min_le_left _ _)
      times radii hdense hpos hcofinal μ hμ
  filter_upwards [hdom, hocc] with ω hωdom hωocc
  exact ⟨hωdom, hωocc⟩
end
