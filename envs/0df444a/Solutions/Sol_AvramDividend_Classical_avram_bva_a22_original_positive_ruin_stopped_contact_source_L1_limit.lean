-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_positive_ruin_stopped_contact_source_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:47:19.302195+00:00
-- url     : https://prove2.me/submissions/e6470b08-2b81-4ebf-a97c-54e023f25e43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun m => T / ((m : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Contact : ℕ → Ω → ℝ := fun m ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal - δ m)
          ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    Tendsto (fun m => ∫ ω, Contact m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro δ S Contact
  have hSpos : 0 < (⟨T, le_of_lt hT⟩ : ℝ≥0) := hT
  convert avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
      X x C D hD q hq ⟨T, le_of_lt hT⟩ hSpos using 1 <;> rfl
