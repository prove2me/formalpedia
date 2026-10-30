-- Prove2me | solution 5 for AvramDividend.Classical.unbounded_corrected_exit_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:34:53.977993+00:00
-- url     : https://prove2.me/submissions/94470561-642c-47a9-8799-a00581744e25

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance

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
  -- Principal route: the target's own decomposition pairs Proved
  -- `chat01_unbounded_corrected_exit_ratio_of_stopped_balance` (c59bf6d7),
  -- which turns an uncorrected stopped balance into the corrected scale
  -- ratio, with Open `chat04_unbounded_two_sided_exit_stopped_scale_identity`
  -- (aed50a34) supplying that balance after unfolding the uncorrected
  -- TwoSidedExit wrappers to the raw iInf integral form.
  have hInline :
      twoSidedExitExpectation X q a x =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
    rfl
  have hBalInline :
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
  have hBalance :
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    rw [hInline]
    exact hBalInline
  exact AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
    X q hq W hW hnbv a x ha hx hxa hBalance
