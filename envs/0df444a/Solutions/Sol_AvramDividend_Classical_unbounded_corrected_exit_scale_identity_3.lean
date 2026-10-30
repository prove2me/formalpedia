-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_corrected_exit_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:03:18.752498+00:00
-- url     : https://prove2.me/submissions/a48d95f8-9847-4e6d-8091-036d67db3ef8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectationCorrected X q a x =
      ENNReal.ofReal (W x / W a) := by
  -- Reduction: rewrite the corrected expectation to the uncorrected one via the
  -- Proved bridge `chat04_twoSidedExitExpectation_eq_corrected` (right-to-left),
  -- then divide the Open unbounded stopped identity `aed50a34` by the strictly
  -- positive value `W a` (Proved: `scaleFunction_strict_pos_of_unbounded_variation`).
  -- Principal lemma: chat04_unbounded_two_sided_exit_stopped_scale_identity.
  -- Exact unresolved identity at this level: none (parent frontier: aed50a34 Open,
  -- which has no recorded decomposition and needs a direct strong-Markov proof).
  rw [← AvramDividend.Classical.chat04_twoSidedExitExpectation_eq_corrected X q a x]
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hnbv a ha
  have hmul :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) :=
    AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  have hA0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos).2 hWa)
  have hAtop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hdiv := congrArg
    (fun z : ℝ≥0∞ => z / ENNReal.ofReal (W a)) hmul
  rw [ENNReal.mul_div_cancel_right hA0 hAtop] at hdiv
  calc
    (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
        ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := hdiv
    _ = ENNReal.ofReal (W x / W a) :=
      (ENNReal.ofReal_div_of_pos hWa).symm
