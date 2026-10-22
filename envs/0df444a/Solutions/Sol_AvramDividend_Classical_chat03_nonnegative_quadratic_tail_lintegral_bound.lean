-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_quadratic_tail_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:28:55.052929+00:00
-- url     : https://prove2.me/submissions/a2ed7878-1aac-4229-8f5e-98379f04368b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_pointwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

/-!
Transfer the pointwise quadratic tail domination to a nonnegative
Lebesgue integral, without any finiteness assumption.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (R : ℝ) (hR : 0 < R)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) :
    (∫⁻ ω, ENNReal.ofReal (if R ≤ Y ω then Y ω else 0) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2 / R) ∂P := by
  apply lintegral_mono_ae
  filter_upwards [hY0] with ω hy
  exact ENNReal.ofReal_le_ofReal
    (chat03_nonnegative_quadratic_tail_pointwise R (Y ω) hR hy)
