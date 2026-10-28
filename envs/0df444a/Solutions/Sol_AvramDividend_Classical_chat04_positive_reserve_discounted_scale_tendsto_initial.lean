-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_discounted_scale_tendsto_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:55:45.95652+00:00
-- url     : https://prove2.me/submissions/a2441ac1-d2b4-4a0b-a500-375f6e3d2303

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

/-- From positive capital, the discounted scale payoff converges pathwise to its
initial value. This gives the positive-reserve initial continuity for the
history-killed q-scale renewal identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) (ω : Ω) :
    Filter.Tendsto
      (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      (𝓝 0) (𝓝 (W x)) := by
  have hpath := X.rightCont ω 0
  have hIci : Ici (0 : ℝ≥0) = univ :=
    Set.eq_univ_of_forall fun t => zero_le (a := t)
  rw [hIci, continuousWithinAt_univ] at hpath
  have harg : ContinuousAt (fun t : ℝ≥0 => x + X.X t ω) 0 :=
    continuousAt_const.add hpath
  have hWc : ContinuousAt W x :=
    scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx)
  have hW0 : ContinuousAt W (x + X.X 0 ω) := by
    simpa [X.X_zero] using hWc
  have hcomp : ContinuousAt
      (W ∘ (fun t : ℝ≥0 => x + X.X t ω)) 0 :=
    ContinuousAt.comp hW0 harg
  have hw : ContinuousAt (fun t : ℝ≥0 => W (x + X.X t ω)) 0 := by
    simpa only [Function.comp_def] using hcomp
  have he : ContinuousAt (fun t : ℝ≥0 =>
      Real.exp (-(q * (t : ℝ)))) 0 := by
    fun_prop
  have hprod := he.mul hw
  have hfun :
      (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) =
      (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ)))) *
        (fun t : ℝ≥0 => W (x + X.X t ω)) := by
    funext t
    simp only [Pi.mul_apply]
  rw [hfun]
  simpa [X.X_zero] using hprod.tendsto
