-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_positive_tail_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:03:57.027117+00:00
-- url     : https://prove2.me/submissions/50800928-7e25-4d70-9d64-b867e8d8951a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Every strictly positive cutoff has finite positive-jump intensity
under the truncated-square Lévy hypothesis. -/
theorem solution (μ : Measure ℝ) (ε : ℝ) (hε : 0 < ε)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    μ (Ici ε) < ⊤ := by
  let c : ℝ := min 1 (ε ^ 2)
  let F : ℝ → ENNReal := fun z =>
    ENNReal.ofReal (min 1 (z ^ 2))
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (sq_pos_of_pos hε)
  have hmono : (∫⁻ z in Ici ε, ENNReal.ofReal c ∂μ) ≤
      (∫⁻ z in Ici ε, F z ∂μ) := by
    apply lintegral_mono_ae
    filter_upwards
      [ae_restrict_mem (μ := μ) (measurableSet_Ici : MeasurableSet (Ici ε))]
      with z hz
    have hsq : ε ^ 2 ≤ z ^ 2 := by
      have hz0 : 0 ≤ z := le_trans hε.le hz
      have hprod := mul_nonneg (sub_nonneg.mpr hz)
        (add_nonneg hε.le hz0)
      nlinarith
    have hmin : c ≤ min (1 : ℝ) (z ^ 2) := by
      dsimp [c]
      exact le_min (min_le_left _ _)
        ((min_le_right _ _).trans hsq)
    exact ENNReal.ofReal_le_ofReal hmin
  have hsub : Ici ε ⊆ Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_lt_of_le hε hz
  have hrestricted : (∫⁻ z in Ici ε, F z ∂μ) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hsub) hlevy
  have hconst : (∫⁻ z in Ici ε, ENNReal.ofReal c ∂μ) =
      ENNReal.ofReal c * μ (Ici ε) := by simp
  have hprod : ENNReal.ofReal c * μ (Ici ε) < ⊤ := by
    rw [← hconst]
    exact lt_of_le_of_lt hmono hrestricted
  rcases ENNReal.mul_lt_top_iff.mp hprod with hfin | hzero | hzero
  · exact hfin.2
  · exact False.elim ((ne_of_gt (ENNReal.ofReal_pos.mpr hc)) hzero)
  · simpa [hzero]
