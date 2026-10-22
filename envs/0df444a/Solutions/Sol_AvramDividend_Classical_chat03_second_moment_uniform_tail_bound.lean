-- Prove2me | solution 1 for AvramDividend.Classical.chat03_second_moment_uniform_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:45:55.154024+00:00
-- url     : https://prove2.me/submissions/9334596e-0066-42c8-81fc-d3f6b0c8ba33

import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_chat03_quadratic_lintegral_threshold_factorisation
import Theorems.Thm_AvramDividend_Classical_chat03_quadratic_moment_lintegral_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

/-!
The upper tail integral of an almost-everywhere nonnegative quantity
is bounded uniformly by its real quadratic-moment bound divided by R.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (R C : ℝ) (hR : 0 < R)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P ∧
      ∫ ω, (Y ω) ^ 2 ∂P ≤ C) :
    (∫⁻ ω, ENNReal.ofReal (if R ≤ Y ω then Y ω else 0) ∂P) ≤
      ENNReal.ofReal C / ENNReal.ofReal R := by
  calc
    (∫⁻ ω, ENNReal.ofReal (if R ≤ Y ω then Y ω else 0) ∂P) ≤
        (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2 / R) ∂P) :=
      chat03_nonnegative_quadratic_tail_lintegral_bound P Y R hR hY0
    _ = (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) /
          ENNReal.ofReal R :=
      chat03_quadratic_lintegral_threshold_factorisation P Y R hR
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal R := by
      gcongr
      exact chat03_quadratic_moment_lintegral_le P Y C hY2
