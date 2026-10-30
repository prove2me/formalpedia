-- Prove2me | solution 6 for AvramDividend.Classical.unbounded_corrected_exit_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:00:51.282766+00:00
-- url     : https://prove2.me/submissions/8d65c666-1a3a-43a6-bef1-ac62ce664346

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity

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
  have hRaw :=
    AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  -- hRaw's raw-⨅ integral is definitionally twoSidedExitExpectation
  -- (UpTime/DownTime unfold to exactly those ⨅ terms), so `exact`
  -- checks it up to defeq; the prior `simpa [...] using hRaw`
  -- half-unfolded and mismatched the `ite` decidability instance (CE E01).
  have hBal : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) :=
    hRaw
  exact AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
    X q hq W hW hnbv a x ha hx hxa hBal
