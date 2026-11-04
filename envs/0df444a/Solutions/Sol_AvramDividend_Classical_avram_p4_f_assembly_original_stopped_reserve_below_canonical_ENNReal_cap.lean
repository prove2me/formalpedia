-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_stopped_reserve_below_canonical_ENNReal_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:01:53.423483+00:00
-- url     : https://prove2.me/submissions/0fe85cb6-1821-4424-b99b-27d99eccea3d

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original postpayment/ruin terminal reserve respects any finite or
    infinite ENNReal cap. The finite case uses the genuine source invariant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ENNReal.ofReal (W ω) ≤ C := by
  by_cases hCtop : C = ⊤
  · intro ω
    simp [hCtop]
  · have hCeq : ENNReal.ofReal C.toReal = C :=
      ENNReal.ofReal_toReal hCtop
    have hDreal : IsAdmissibleLe X x (ENNReal.ofReal C.toReal) D := by
      simpa only [hCeq] using hD
    have hxreal : ENNReal.ofReal x ≤ ENNReal.ofReal C.toReal := by
      simpa only [hCeq] using hxc
    intro ω
    have hWreal : W ω ≤ C.toReal :=
      avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
        X x C.toReal ENNReal.toReal_nonneg hxreal D hDreal τ W hW ω
    rw [← hCeq]
    exact ENNReal.ofReal_mono hWreal