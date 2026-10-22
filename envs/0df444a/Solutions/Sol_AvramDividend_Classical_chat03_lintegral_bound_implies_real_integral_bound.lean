-- Prove2me | solution 1 for AvramDividend.Classical.chat03_lintegral_bound_implies_real_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:07:22.570373+00:00
-- url     : https://prove2.me/submissions/ebce6291-559c-4c90-ba7c-bae27ca38364

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-!
Convert a finite extended-nonnegative integral estimate to a bound
on the real Bochner integral of an integrable nonnegative function.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (C : ℝ)
    (hfi : Integrable f P) (hf0 : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hC : 0 ≤ C)
    (hbound : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal C) :
    (∫ ω, f ω ∂P) ≤ C := by
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hfi hf0]
  exact hbound
