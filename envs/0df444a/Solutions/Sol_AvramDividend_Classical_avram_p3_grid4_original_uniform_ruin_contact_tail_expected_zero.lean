-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_uniform_ruin_contact_tail_expected_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:43:24.252015+00:00
-- url     : https://prove2.me/submissions/79be014b-6211-4b40-998d-d099bef2d67e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Expected original strict dividend cash in the ruin-contact cell
vanishes for the exact uniform physical-mesh width T/(n+2). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal -
                (T : ℝ) / ((n : ℝ) + 2))
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  obtain ⟨hpos, _, hanti, hlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence (T : ℝ) hTreal
  simpa only [] using
    (avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
      X x C D hD q hq T
      (fun n => (T : ℝ) / ((n : ℝ) + 2)) hpos hanti hlim)
