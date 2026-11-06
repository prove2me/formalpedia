-- Prove2me | solution 15 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:06:08.034133+00:00
-- url     : https://prove2.me/submissions/1e45925e-d4e8-4791-9f4b-08e4587d6347
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_or_local_cstar_original_capped_optimality

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Root-connected finite-cstar capped bound, retaining the genuine local stochastic dependency. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  have hEither :
      cstar W = 0 ∨
        (∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
          valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) := by
    by_cases hzero : cstar W = 0
    · exact Or.inl hzero
    · right
      have hpos : 0 < cstar W := lt_of_le_of_ne bot_le (Ne.symm hzero)
      obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
        vcstar_local_verification_regular_of_positive_cstar
          X hX q hq W hW hc hpos h_smooth
      have hHJB := vcstar_hjb_below_positive_cstar
        X hX q hq W hW hc h_smooth hpos
      have hVerify := local_verification
        X hX q hq (vcstar W) (cstar W)
          hpos hcont hw0 hwneg hsmooth hHJB
      intro x hx hxc
      apply hVerify.1 x hx
      calc
        ENNReal.ofReal x ≤ ENNReal.ofReal (cstar W).toReal :=
          ENNReal.ofReal_le_ofReal hxc
        _ = cstar W := ENNReal.ofReal_toReal (ne_of_lt hc)
  intro x hx
  exact le_of_eq
    (avram_sweep16_zero_or_local_cstar_original_capped_optimality
      X hX q hq W hW hc h_smooth hEither x hx)
