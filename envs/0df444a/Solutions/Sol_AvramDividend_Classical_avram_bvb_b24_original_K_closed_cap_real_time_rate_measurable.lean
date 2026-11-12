-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b24_original_K_closed_cap_real_time_rate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:25:58.766201+00:00
-- url     : https://prove2.me/submissions/4d49c16e-7664-47c2-8fda-289bf43ede54

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_prepayment_leftlim_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original stopped closed-cap negative-mark K time density is Borel measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q T : ℝ) (hT : 0 < T) (n : ℕ) (ψ : ℝ → ℝ)
    (hψ : ContinuousOn ψ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then
        Real.exp (-(q * (t : ℝ))) * ψ (U t)
      else 0) := by
  intro U
  have hstrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hU : Measurable U :=
    avram_bvb_b22_original_prepayment_leftlim_path_measurable
      X x D hstrategy ω
  exact avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
    C (ruinTime X x D ω) q T hT n U U hU
    (by intro t ht htT; rfl) ψ hψ
