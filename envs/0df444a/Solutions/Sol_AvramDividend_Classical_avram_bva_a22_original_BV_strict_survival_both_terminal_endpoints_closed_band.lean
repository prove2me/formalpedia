-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_strict_survival_both_terminal_endpoints_closed_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:23.778128+00:00
-- url     : https://prove2.me/submissions/b329600c-5d62-4490-b106-1b1750e27928

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      (x + X.X (u m (m + 1)) ω -
        rightLimit D (u m (m + 1)) ω) ∈
          Icc (0 : ℝ) (x + T * X.drift) ∧
      (x + X.X S ω - rightLimit D S ω) ∈
          Icc (0 : ℝ) (x + T * X.drift) := by
  dsimp only
  filter_upwards
    [avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
      X hX hBV x C hxc D hD ⟨T, le_of_lt hT⟩] with ω hω
  intro m hsurvive
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hstep : ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
    push_cast
    linarith
  have hlast : u m (m + 1) ≤ S := by
    change (u m (m + 1) : ℝ) ≤ T
    rw [huniform m (m + 1)]
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left hstep (le_of_lt hT)
  have hlastENN : (u m (m + 1) : ℝ≥0∞) ≤ (S : ℝ≥0∞) := by
    exact_mod_cast hlast
  have hBefore :
      (u m (m + 1) : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_le_of_lt hlastENN hsurvive
  have hLast := hω (u m (m + 1)) hlast (Or.inr hBefore)
  have hTrue := hω S le_rfl (Or.inr hsurvive)
  exact ⟨⟨hLast.1, hLast.2.2⟩,
    ⟨hTrue.1, hTrue.2.2⟩⟩
