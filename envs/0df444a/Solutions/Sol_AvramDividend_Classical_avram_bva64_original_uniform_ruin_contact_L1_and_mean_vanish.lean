-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:59:50.828896+00:00
-- url     : https://prove2.me/submissions/d8396f85-c703-4b6e-99b5-9631fb93019e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hTpos : 0 < T) :
    (∀ n : ℕ, Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal -
               (T : ℝ) / ((n : ℝ) + 2))
            ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) P) ∧
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal -
                 (T : ℝ) / ((n : ℝ) + 2))
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  constructor
  · intro n
    have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
    obtain ⟨hτM, hτBounds⟩ :=
      avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
        X x D hDiv T
    exact
      avram_p3_grid3_original_random_strict_contact_tail_real_integrable
        X x C D hD q hq T
        (fun ω => (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal)
        hτM (fun ω => (hτBounds ω).1) (fun ω => (hτBounds ω).2)
        ((T : ℝ) / ((n : ℝ) + 2))
  · exact
      avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
        X x C D hD q hq T hTpos

