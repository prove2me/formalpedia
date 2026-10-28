-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:53:59.424222+00:00
-- url     : https://prove2.me/submissions/759f419e-488e-4d61-85e8-d7b74ded3035

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_random_clock_stopped_density_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (τ : Ω → ℝ≥0) (ω : Ω) (t : ℝ)
    (hObs : (τ ω : ℝ) ≤ t) :
    ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal t) ω -
      (Real.toNNReal t : ℝ) * X.ψ θ)) =
    ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)) *
    ENNReal.ofReal (Real.exp (θ *
      (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω -
       X.X (τ ω) ω) -
      (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ)) := by
  have ht0 : 0 ≤ t :=
    le_trans (NNReal.coe_nonneg (τ ω)) hObs
  have hdelta0 : 0 ≤ t - (τ ω : ℝ) := sub_nonneg.mpr hObs
  have htime :
      Real.toNNReal t = τ ω + Real.toNNReal (t - (τ ω : ℝ)) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add]
    rw [Real.coe_toNNReal _ ht0, Real.coe_toNNReal _ hdelta0]
    ring
  have hObsNN : τ ω ≤ Real.toNNReal t := by
    rw [htime]
    exact le_add_of_nonneg_right zero_le
  have hdelta :
      Real.toNNReal t - τ ω = Real.toNNReal (t - (τ ω : ℝ)) := by
    rw [htime]
    exact add_tsub_cancel_left (τ ω) _
  have hs :=
    avram_ws01e_b_esscher_random_clock_stopped_density_split
      X θ τ Real.toNNReal ω t hObsNN
  have hEN := congrArg ENNReal.ofReal hs
  rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))] at hEN
  rw [hdelta] at hEN
  simpa only [← htime, SpectrallyNegativeLevy.ψ] using hEN
