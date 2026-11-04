-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:21:20.514744+00:00
-- url     : https://prove2.me/submissions/0c5ba2a2-5c9a-499b-90c1-79115891c0fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite physical Lévy mark intensity and the genuine original jump-count
rate imply real first-moment integrability and almost-sure finiteness for
the same source marked count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (hMeas : Measurable J)
    (hRate : (∫⁻ ω, J ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hFinite : X.ν B ≠ ⊤) :
    Integrable (fun ω => (J ω).toReal) P ∧
      (∀ᵐ ω ∂P, J ω < ⊤) := by
  have hMeanFinite : (∫⁻ ω, J ω ∂P) ≠ ⊤ := by
    rw [hRate]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hFinite
  exact ⟨integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable hMeanFinite,
    ae_lt_top hMeas hMeanFinite⟩
