-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_all_positive_zero_barrier_of_nearfield
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:23:56.204454+00:00
-- url     : https://prove2.me/submissions/fb540b71-b86a-463e-9b80-14a4097c5c63

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_nonpos_zero_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Far-field generator control reduces the zero-barrier HJB inequality
to the near-origin or insufficient-discount region. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (hnear : ∀ y : ℝ, 0 < y → (y < 1 ∨ q * y < X.c) →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  intro y hy
  have hgen : X.GeneratorIntegrable (vcstar W) y ∧
      X.generator (vcstar W) y - q * vcstar W y ≤ 0 := by
    by_cases hy1 : 1 ≤ y
    · by_cases hcost : X.c ≤ q * y
      · exact vcstar_far_field_generator_nonpos_zero_barrier
          X hX q hq W hW hc0 y hy1 hcost
      · exact hnear y hy (Or.inr (lt_of_not_ge hcost))
    · exact hnear y hy (Or.inl (lt_of_not_ge hy1))
  have hderiv : deriv (vcstar W) y = 1 :=
    vcstar_deriv_eq_one_above_cstar W y (by simpa [hc0] using hy)
  refine ⟨hgen.1, ?_⟩
  simpa [hderiv] using (max_eq_right hgen.2)
