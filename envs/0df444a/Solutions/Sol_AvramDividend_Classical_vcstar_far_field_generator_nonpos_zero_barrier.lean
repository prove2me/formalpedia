-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_far_field_generator_nonpos_zero_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:13:01.642513+00:00
-- url     : https://prove2.me/submissions/be796dc8-a8d2-4d89-b366-55b39a834d2c

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_residual_nonpos_of_monotone
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At a zero barrier, monotonicity controls large negative jumps and the
nonnegative boundary value makes the affine part dominate the drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (x : ℝ) (hx : 1 ≤ x) (hcost : X.c ≤ q * x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_zero_cstar X hX q hq W hW hc0
  have hx0 : 0 ≤ x := by linarith
  have hb : 0 ≤ barrierValue W 0 0 :=
    barrierValue_nonnegative_for_nonnegative_capital
      X hX q hq W hW 0 0 le_rfl le_rfl
  have hvalue : vcstar W x = x + barrierValue W 0 0 := by
    change barrierValue W (cstar W).toReal x = _
    simpa [hc0] using barrierValue_zero_affine_nonnegative W x hx0
  have hbound : X.c ≤ q * vcstar W x := by
    rw [hvalue]
    nlinarith [mul_nonneg (le_of_lt hq) hb]
  have hfar : (cstar W).toReal + 1 ≤ x := by
    simpa [hc0] using hx
  exact vcstar_far_field_generator_residual_nonpos_of_monotone
    X q W hW hmono x hfar hbound
