-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger40_original_bounded_stop_strict_last_cell_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:42:15.397605+00:00
-- url     : https://prove2.me/submissions/4afda6c2-51b3-42ff-a409-4ffff60ad212

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uniform_strict_delta_antitone_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical last-cell cash is strict at the original stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    Tendsto (fun m : ℕ =>
      ∫ ω : Ω, (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ ω : ℝ) - (n : ℝ) / ((m : ℝ) + 2)) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let δ : ℕ → ℝ := fun m => (n : ℝ) / ((m : ℝ) + 2)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hδpos, hδanti, hδ0⟩ :=
    avram_p3_grid4_uniform_strict_delta_antitone_vanishes (n : ℝ) hnR
  have hρmeas : Measurable (fun ω : Ω => (ρ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable ρ hρstop
  have hρ0 (ω : Ω) : (0 : ℝ) ≤ (ρ ω : ℝ) := by positivity
  have hρT (ω : Ω) : (ρ ω : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hρbound ω
  simpa only [δ] using
    (avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
      X x C D hD q hq (n : ℝ≥0) (fun ω => (ρ ω : ℝ))
      hρmeas hρ0 hρT δ (fun m => (hδpos m).1) hδanti hδ0)
