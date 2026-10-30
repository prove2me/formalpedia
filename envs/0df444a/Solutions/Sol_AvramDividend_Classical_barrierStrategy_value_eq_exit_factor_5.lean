-- Prove2me | solution 5 for AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T02:44:11.466353+00:00
-- url     : https://prove2.me/submissions/cc5a7d72-6c75-40bf-9e0d-d1c5fd5d2076

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / W a) * barrierSupValue X a q := by
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
  have hexit : (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) = ENNReal.ofReal (W x / W a) :=
    AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
      X hX q hq W hW a x ha hx0 hxa
  rw [hkill, hexit]
