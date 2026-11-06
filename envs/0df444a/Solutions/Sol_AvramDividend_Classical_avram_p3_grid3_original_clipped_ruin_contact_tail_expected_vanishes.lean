-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:00:39.284188+00:00
-- url     : https://prove2.me/submissions/f46e4030-27cc-43a7-84ef-09c94ab7b78f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine ruin-clipped contact cash has vanishing mean as the strict band shrinks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal - δ n)
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  obtain ⟨hτM, hτBounds⟩ :=
    avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
      X x D hDiv T
  exact
    avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
      X x C D hD q hq T
      (fun ω => (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal)
      hτM (fun ω => (hτBounds ω).1) (fun ω => (hτBounds ω).2)
      δ hδpos hδanti hδ
