-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_far_field_hjb_of_reserve_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:42:01.012611+00:00
-- url     : https://prove2.me/submissions/cfadc6a0-03a7-466c-97cb-f55951fe57b5

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_hjb_of_finite_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The value at the barrier is nonnegative, so the affine continuation
dominates the excess reserve and gives an explicit far-field drift test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x)
    (hdrift : X.c ≤ q * (x - (cstar W).toReal)) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hx : a < x := by
    dsimp [a]
    linarith
  have hb : 0 ≤ barrierValue W a a :=
    barrierValue_nonnegative_for_nonnegative_capital
      X hX q hq W hW a a ha ha
  have hboundary : barrierValue W a a =
      divE (W a) (scaleDeriv W a) := by
    simp [barrierValue, not_lt.mpr ha]
  have hval : vcstar W x = x - a + barrierValue W a a := by
    calc
      vcstar W x = x - a + divE (W a) (scaleDeriv W a) :=
        vcstar_eq_linear_gt_cstar W x hx
      _ = x - a + barrierValue W a a := by rw [hboundary]
  have hle : x - a ≤ vcstar W x := by rw [hval]; linarith
  have hcost : X.c ≤ q * vcstar W x :=
    le_trans hdrift (mul_le_mul_of_nonneg_left hle hq.le)
  exact vcstar_far_field_hjb_of_finite_cstar
    X hX q hq W hW hcfin x hfar hcost
