-- Prove2me | solution 1 for DuchiSIT.dobrushin_le_tvContraction
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T18:25:27.297488+00:00
-- url     : https://prove2.me/submissions/256afeec-6061-4340-848e-b4cc9b13f28c

import Theorems.Thm_DuchiSIT_tv_probability_bounds
import Theorems.Thm_MarkovChainCLT_tvDist_comp_le
import Definitions.Def_DuchiSIT_TVContractionCoefficient
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

open DuchiSIT


theorem solution {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] :
    dobrushin K ≤ tvContraction K := by
  classical
  have h0 : 0 ≤ tvContraction K := by
    apply Real.sSup_nonneg
    rintro r ⟨μ, ν, hne, rfl⟩
    exact div_nonneg (DuchiSIT.tv_probability_bounds (channel K μ : Measure Y) (channel K ν : Measure Y)).2.1
      (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.1
  have hbound (μ ν : ProbabilityMeasure X) (hne : μ ≠ ν) :
      MarkovChainCLT.tvDist (channel K μ : Measure Y) (channel K ν : Measure Y) /
        MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X) ≤ 1 := by
    have hn := MarkovChainCLT.tvDist_comp_le K (μ : Measure X) (ν : Measure X)
    have hd := (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.1
    exact (div_le_one₀ (lt_of_le_of_ne hd (by
      intro he
      apply hne
      apply ProbabilityMeasure.toMeasure_injective
      exact (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.2.2.mp he.symm))).mpr hn
  have hb : BddAbove {r : ℝ | ∃ μ ν : ProbabilityMeasure X, μ ≠ ν ∧
      r = MarkovChainCLT.tvDist (channel K μ : Measure Y) (channel K ν : Measure Y) /
        MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X)} := by
    refine ⟨1, ?_⟩
    rintro r ⟨μ, ν, hne, rfl⟩
    exact hbound μ ν hne
  apply Real.sSup_le _ h0
  rintro r ⟨x, y, rfl⟩
  let μ : ProbabilityMeasure X := ⟨Measure.dirac x, inferInstance⟩
  let ν : ProbabilityMeasure X := ⟨Measure.dirac y, inferInstance⟩
  have hx : (channel K μ : Measure Y) = K x := Measure.dirac_bind K.measurable x
  have hy : (channel K ν : Measure Y) = K y := Measure.dirac_bind K.measurable y
  by_cases he : μ = ν
  · have hr : K x = K y := by rw [← hx, ← hy, he]
    have hz := (DuchiSIT.tv_probability_bounds (K x) (K y)).2.2.2.mpr hr
    rw [hz]
    exact h0
  · have hd0 := (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.1
    have hd1 := (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.2.1
    have hdp : 0 < MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X) := by
      apply lt_of_le_of_ne hd0
      intro hz
      apply he
      apply ProbabilityMeasure.toMeasure_injective
      exact (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.2.2.mp hz.symm
    have hr0 := (DuchiSIT.tv_probability_bounds (K x) (K y)).2.1
    have hratio : MarkovChainCLT.tvDist (K x) (K y) ≤
        MarkovChainCLT.tvDist (channel K μ : Measure Y) (channel K ν : Measure Y) /
        MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X) := by
      rw [hx, hy, le_div_iff₀ hdp]
      exact mul_le_of_le_one_right hr0 hd1
    apply hratio.trans
    exact le_csSup hb ⟨μ, ν, he, rfl⟩
