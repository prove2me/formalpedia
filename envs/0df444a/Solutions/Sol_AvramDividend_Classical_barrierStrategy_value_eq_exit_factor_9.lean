-- Prove2me | solution 9 for AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:57:17.665065+00:00
-- url     : https://prove2.me/submissions/95c39362-cc4d-486a-8e13-4c323bf78fc3

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

-- Exit factor via killed-exit factorisation + integral identity.
-- Variant u (2026-10-29): top-level rewrite architecture over prior calc file.
-- hkill (Open 8fc83520): divVal x = E * supValue, with E the discounted
-- two-sided-exit lintegral. hexit (Open 3e1ce2c8): E = ofReal (W x / W a).
-- `rw [hkill, hexit]` closes the goal; no calc block, fully explicit args.
-- Mathematics unchanged from direct_supValue; elaboration path distinct.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION. No local Lean was run.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / W a) * barrierSupValue X a q := by
  have hkill :
      dividendValue X q x (barrierStrategy X x a) =
        (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) * barrierSupValue X a q :=
    AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
      X hX q hq a x ha hx0 hxa
  have hexit :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
        ENNReal.ofReal (W x / W a) :=
    AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
      X hX q hq W hW a x ha hx0 hxa
  rw [hkill]
  rw [hexit]
