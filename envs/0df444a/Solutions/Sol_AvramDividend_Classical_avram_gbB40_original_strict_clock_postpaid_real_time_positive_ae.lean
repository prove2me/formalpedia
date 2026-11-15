-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:48:36.684606+00:00
-- url     : https://prove2.me/submissions/ff6efe35-b465-449a-8272-1468ca3c534d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ t : ℝ≥0, 0 < t → t < ρ →
      δ ≤ riskProcess X x D t ω) :
    let S : Set ℝ := {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ : ℝ)}
    ∀ᵐ t ∂(volume.restrict S),
      0 < x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω := by
  let S : Set ℝ := {t : ℝ |
    0 < t ∧ t < (n : ℝ) ∧ t < (ρ : ℝ)}
  change ∀ᵐ t ∂(volume.restrict S),
    0 < x + X.X (Real.toNNReal t) ω -
      rightLimit D (Real.toNNReal t) ω
  have hSm : MeasurableSet S := by
    dsimp [S]
    measurability
  have hp :=
    avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω ρ δ hFloor
  filter_upwards [ae_restrict_mem hSm] with t ht
  rcases ht with ⟨ht0, htn, htρ⟩
  have htime : Real.toNNReal t < ρ := by
    apply NNReal.coe_lt_coe.mp
    rw [Real.coe_toNNReal t (le_of_lt ht0)]
    exact htρ
  exact lt_of_lt_of_le hδ (hp (Real.toNNReal t) htime)
