-- Prove2me | solution 10 for AvramDividend.Classical.admissible_cap_nat_horizon_bound_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:13:26.218799+00:00
-- url     : https://prove2.me/submissions/4e3f9788-60f5-4562-987e-c3dff2831f5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_UBV_natclock_given_true_discounted_terminal_envelopes
import Theorems.Thm_AvramDividend_Classical_avram_limit2_discounted_terminal_vanish_of_finite_stochastic_envelope
import Theorems.Thm_AvramDividend_Classical_avram_limit2_discounted_terminal_vanish_of_uniform_expected_payoffs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  apply AvramDividend.Classical.avram_bridge20261122_UBV_natclock_given_true_discounted_terminal_envelopes X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hD
  exact ⟨AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_finite_stochastic_envelope P q hq,
    AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_uniform_expected_payoffs P q hq⟩
