-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_cross_derivative_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:48:03.407587+00:00
-- url     : https://prove2.me/submissions/ad3f71d9-b733-4489-9b9b-0f7c447dca73

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
import Theorems.Thm_AvramDividend_Classical_positive_ratio_order_cross_derivative_le
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The killed-exit ratio ordering yields a local q-scale slope inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hdx : DifferentiableAt ℝ W x)
    (hdy : DifferentiableAt ℝ W y) :
    deriv W y * W x ≤ deriv W x * W y := by
  have hpos : ∀ z : ℝ, 0 < z → 0 < W z :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hratio : ∀ u v t : ℝ, 0 < u → u ≤ v → 0 < t →
      W u / W (u + t) ≤ W v / W (v + t) := by
    intro u v t hu huv ht
    have hv : 0 < v := lt_of_lt_of_le hu huv
    have hut : 0 < u + t := by linarith
    have hvt : 0 < v + t := by linarith
    have hule : u ≤ u + t := by linarith
    have hvle : v ≤ v + t := by linarith
    have hmono :
        twoSidedExitExpectationCorrected X q (u + t) u ≤
        twoSidedExitExpectationCorrected X q (v + t) v := by
      simpa [add_comm] using
        (corrected_exit_shifted_initial_reserve_monotone X q t u v huv)
    rw [hExit (u + t) u hut hu hule,
        hExit (v + t) v hvt hv hvle] at hmono
    exact (ENNReal.ofReal_le_ofReal_iff
      (le_of_lt (div_pos (hpos v hv) (hpos (v + t) hvt)))).mp hmono
  exact positive_ratio_order_cross_derivative_le
    W hpos hratio x y hx hxy hdx hdy
