-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_far_field_hjb_zero_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:20:20.847743+00:00
-- url     : https://prove2.me/submissions/9d730e3f-ae8e-44b8-af54-2e19a723ffff

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_nonpos_zero_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The full HJB maximum vanishes in the verified zero-barrier far field:
the generator residual is nonpositive and the affine derivative is one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (x : ℝ) (hx : 1 ≤ x) (hcost : X.c ≤ q * x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  obtain ⟨hint, hnonpos⟩ :=
    vcstar_far_field_generator_nonpos_zero_barrier
      X hX q hq W hW hc0 x hx hcost
  have hxpos : 0 < x := by linarith
  have hderiv : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x (by simpa [hc0] using hxpos)
  refine ⟨hint, ?_⟩
  simpa [hderiv] using (max_eq_right hnonpos)
