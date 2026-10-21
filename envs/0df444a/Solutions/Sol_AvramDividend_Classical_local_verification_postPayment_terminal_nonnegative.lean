-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_postPayment_terminal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:31:09.671524+00:00
-- url     : https://prove2.me/submissions/02e06f80-e0ca-43bd-af56-9e15ee35dd4b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_candidate_lower_bound_on_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (x + X.X t ω - rightLimit D t ω) := by
  let y : ℝ := x + X.X t ω - rightLimit D t ω
  have hyC : ENNReal.ofReal y ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  by_cases hy : 0 ≤ y
  · exact (local_verification_hjb_candidate_lower_bound_on_cap
      X q w C hw_cont hw0 hw_smooth hw_hjb y hy hyC).2
  · have hneg : y < 0 := lt_of_not_ge hy
    rw [hw_neg y hneg]
