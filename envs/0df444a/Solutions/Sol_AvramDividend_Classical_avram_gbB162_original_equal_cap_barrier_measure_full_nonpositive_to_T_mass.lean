-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB162_original_equal_cap_barrier_measure_full_nonpositive_to_T_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:28:25.900969+00:00
-- url     : https://prove2.me/submissions/49b6e57e-42cb-426b-9518-39f2e3229681

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_cap_barrier_full_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
noncomputable section
/-- True original equal-cap barrier measure through T is cumulative dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c : ℝ) (ω : Ω) (T : ℝ≥0) :
    dividendMeasure (barrierStrategy X c c) ω
      (Iic (T : ℝ)) =
    ENNReal.ofReal (barrierStrategy X c c T ω) := by
  let D := barrierStrategy X c c
  have hMono : Monotone (fun t : ℝ => D t.toNNReal ω) := by
    intro a b hab
    exact (barrierStrategy_monotone X c ω) (Real.toNNReal_mono hab)
  have hCont : Continuous (fun t : ℝ => D t.toNNReal ω) :=
    (avram_gbB32_original_cap_barrier_full_continuity X c ω).comp
      continuous_real_toNNReal
  have hEqFun :
      ((hMono.stieltjesFunction : StieltjesFunction ℝ) : ℝ → ℝ) =
        (fun t : ℝ => D t.toNNReal ω) := by
    funext t
    rw [Monotone.stieltjesFunction_eq]
    exact (hCont.continuousAt.continuousWithinAt).rightLim_eq
  have hEv : ∀ᶠ t : ℝ in atBot, D t.toNNReal ω = 0 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    simp [D, barrierStrategy, Real.toNNReal_of_nonpos (le_of_lt ht)]
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
