-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_any_finite_barrier_dividendMeasure_Iic_eq_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:34:54.952467+00:00
-- url     : https://prove2.me/submissions/cd8b2e99-edff-4e54-885c-acca7549bef9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (T : ℝ≥0) :
    dividendMeasure (barrierStrategy X x a) ω (Iic (T : ℝ)) =
      ENNReal.ofReal (barrierStrategy X x a T ω) := by
  let D := barrierStrategy X x a
  have hMono : Monotone (fun t : ℝ => D t.toNNReal ω) := by
    intro a' b' hab
    exact (barrierStrategy_monotone_of_le X x a hxa ω)
      (Real.toNNReal_mono hab)
  have hRight : ∀ r : ℝ,
      Function.rightLim (fun s : ℝ => D s.toNNReal ω) r =
        D r.toNNReal ω :=
    rightLim_comp_toNNReal_of_rightContinuous
      (fun t : ℝ≥0 => D t ω)
      (barrierStrategy_right_continuous_of_le X x a hxa ω)
  have hEqFun :
      ((hMono.stieltjesFunction : StieltjesFunction ℝ) : ℝ → ℝ) =
        (fun t : ℝ => D t.toNNReal ω) := by
    funext t
    rw [Monotone.stieltjesFunction_eq]
    exact hRight t
  have hEv : ∀ᶠ t : ℝ in atBot, D t.toNNReal ω = 0 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    simp [D, barrierStrategy, Real.toNNReal_of_nonpos (le_of_lt ht),
      max_eq_left (sub_nonpos.mpr hxa)]
  have hTend : Tendsto (fun t : ℝ => D t.toNNReal ω)
      atBot (nhds (0 : ℝ)) := by
    exact tendsto_const_nhds.congr' (hEv.mono fun t ht => ht.symm)
  have hSt :
      Tendsto ((hMono.stieltjesFunction : StieltjesFunction ℝ) : ℝ → ℝ)
        atBot (nhds (0 : ℝ)) := by
    rw [hEqFun]
    exact hTend
  have hMass :=
    StieltjesFunction.measure_Iic hMono.stieltjesFunction hSt (T : ℝ)
  unfold dividendMeasure
  rw [dif_pos hMono]
  rw [hEqFun] at hMass
  simpa [D] using hMass
