-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB230_original_floor_lower_clip_strip_exact_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:03.523452+00:00
-- url     : https://prove2.me/submissions/b24f5f6e-839b-4964-a3e1-0471be6fb9ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- No stopped original reserve occupation in a lower strip separated from its floor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεsmall : ε < δ / 2)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ ω : Ω,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - δ / 2) < ε} = 0 := by
  intro ω
  have hAE :=
    avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
      X x D hD ω
  have hNull : ∀ᵐ t : ℝ ∂volume,
      t ∉ {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - δ / 2) < ε} := by
    filter_upwards [hAE] with t hEq
    rintro ⟨ht0, htn, htρ, hAbs⟩
    have hcoe : (Real.toNNReal t : ℝ) = t :=
      Real.coe_toNNReal t (le_of_lt ht0)
    have htNN : 0 < Real.toNNReal t := by
      have hh : (0 : ℝ) < (Real.toNNReal t : ℝ) := by
        simpa only [hcoe] using ht0
      exact_mod_cast hh
    have hρNN : Real.toNNReal t < ρ ω := by
      have hh : (Real.toNNReal t : ℝ) < (ρ ω : ℝ) := by
        simpa only [hcoe] using htρ
      exact_mod_cast hh
    have hFloor' := hFloor ω (Real.toNNReal t) htNN hρNN
    have hRiskEq := hEq (le_of_lt ht0)
    rw [hRiskEq] at hFloor'
    have hUpper := (abs_lt.mp hAbs).2
    linarith
  exact (measure_eq_zero_iff_ae_notMem).2 hNull
