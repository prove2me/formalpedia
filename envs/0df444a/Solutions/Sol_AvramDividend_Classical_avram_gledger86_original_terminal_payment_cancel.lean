-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger86_original_terminal_payment_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:48:14.72944+00:00
-- url     : https://prove2.me/submissions/79aff331-710d-4343-850b-298d830f1e5d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger45_global_topcap_monotone_zero_negative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (ρ a : ℝ≥0)
    (hDiv : rightLimit D a ω ≤ D ρ ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    Real.exp (-(q * (ρ : ℝ))) *
      ((w (x + X.X ρ ω - rightLimit D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) +
        (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D ρ ω))) ≤ 0 := by
  have hstate : riskProcess X x D ρ ω ≤
      x + X.X ρ ω - rightLimit D a ω := by
    dsimp [riskProcess]
    linarith
  have hmono := avram_gledger45_global_topcap_monotone_zero_negative
    w C hTopCap hw0 hw_cont hw_neg hw_grad
    (riskProcess X x D ρ ω)
    (x + X.X ρ ω - rightLimit D a ω) hstate
  calc
    Real.exp (-(q * (ρ : ℝ))) *
      ((w (x + X.X ρ ω - rightLimit D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) +
        (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D ρ ω))) =
      Real.exp (-(q * (ρ : ℝ))) *
        (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (sub_nonpos.mpr hmono)
