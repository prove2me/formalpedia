-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:47:12.352642+00:00
-- url     : https://prove2.me/submissions/2a039cff-47b5-44b4-a1a4-f0192d27efa8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Contact : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal - δ n)
              ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    (∀ m, Integrable (Contact m) P) ∧
      Tendsto (fun m => ∫ ω, Contact m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  intro δ S Contact
  have hS : 0 < S := by exact_mod_cast hT
  exact
    avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
      X x C D hD q (le_of_lt hq) S hS
