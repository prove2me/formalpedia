-- Prove2me | solution 11 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T06:52:32.767981+00:00
-- url     : https://prove2.me/submissions/3c29a5c1-2eb0-4c53-a3db-237efd6fdc72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a)
        = ENNReal.ofReal (W x / W a) * dividendValue X q a (barrierStrategy X a a) := by
  have hPos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  -- Killed-exit factorisation (Open 8fc83520): dividend at x splits into the
  -- discounted two-sided up-exit integral times the barrier supremum value.
  have hkill : dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * barrierSupValue X a q :=
    AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
      X hX q hq a x ha hx0 hxa
  -- Two-sided exit integral identity (Open 3e1ce2c8, SKETCH_ACCEPTED 18065):
  -- the killed integral equals the scale ratio W x / W a.
  have hexit : (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) = ENNReal.ofReal (W x / W a) :=
    AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
      X hX q hq W hW a x ha hx0 hxa
  -- Self value (Proved 11b589b7): dividend at a equals the supremum value.
  have hSelf : dividendValue X q a (barrierStrategy X a a) = barrierSupValue X a q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  refine ⟨hPos, ?_⟩
  rw [hkill, hexit, hSelf]
