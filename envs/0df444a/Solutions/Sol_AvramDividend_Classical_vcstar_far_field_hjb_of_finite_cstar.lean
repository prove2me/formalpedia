-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_far_field_hjb_of_finite_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:34:51.510128+00:00
-- url     : https://prove2.me/submissions/b5c3937b-677f-48ff-8819-47ca5f719b1e

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_residual_nonpos_of_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Far from any finite optimal barrier, the compensated small-jump term
vanishes, while monotonicity controls the large negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x)
    (hcost : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_finite_cstar X hX q hq W hW hcfin
  obtain ⟨hint, hle⟩ :=
    vcstar_far_field_generator_residual_nonpos_of_monotone
      X q W hW hmono x hfar hcost
  have hx : (cstar W).toReal < x := by linarith
  refine ⟨hint, ?_⟩
  rw [vcstar_deriv_eq_one_above_cstar W x hx]
  simpa using (max_eq_right hle)
