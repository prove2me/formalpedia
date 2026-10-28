-- Prove2me | solution 1 for AvramDividend.Classical.chat12_barrierSupValue_le_scale_ratio_geometric_of_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:05:24.103539+00:00
-- url     : https://prove2.me/submissions/58a3a346-384b-4fbc-9484-07c590bdfddb

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_le_closed_form_of_trueExit
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    barrierSupValue X a q ≤
      ENNReal.ofReal ε * (1 - ENNReal.ofReal (W a / W (a + ε)))⁻¹ := by
  have hRatio : 0 ≤ W a / W (a + ε) :=
    div_nonneg hWa (le_of_lt hWright)
  exact chat12_barrierSupValue_le_closed_form_of_trueExit
    X hX q hq a ε ha hε (W a / W (a + ε)) hRatio hExit
