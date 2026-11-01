-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_far_field_generator_residual_le_neg_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:45:09.299549+00:00
-- url     : https://prove2.me/submissions/d3e064d4-bae9-4cea-8750-3494fed8e01f

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An explicit reserve threshold yields a strict source Lévy generator residual margin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ -q := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hmax0 : 0 ≤ max 0 (X.c / q) := le_max_left _ _
  have hfar1 : a + 1 ≤ x := by dsimp [a] at *; linarith
  have hx : a < x := by linarith
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
  have hquot : X.c / q ≤ x - a - 1 := by
    have hmaxq : X.c / q ≤ max 0 (X.c / q) := le_max_right _ _
    change a + 1 + max 0 (X.c / q) ≤ x at hfar
    linarith
  have hcost : X.c ≤ (x - a - 1) * q := (div_le_iff₀ hq).mp hquot
  have hmul := mul_le_mul_of_nonneg_left hle hq.le
  have hqmargin : X.c + q ≤ q * vcstar W x := by
    linarith
  obtain ⟨hdom, hres⟩ :=
    avram_wave4_05_source_far_field_generator_residual_le_drift_minus_discount
      X hX q hq W hW x hfar1
  exact ⟨hdom, by linarith⟩
