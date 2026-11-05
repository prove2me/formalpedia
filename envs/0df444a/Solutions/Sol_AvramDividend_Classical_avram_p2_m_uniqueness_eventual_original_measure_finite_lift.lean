-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_eventual_original_measure_finite_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:57:47.60742+00:00
-- url     : https://prove2.me/submissions/8efc77ab-b16a-405c-ac0e-ea8403ac33fd

import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- An eventually finite original measure family has a globally defined
finite-measure lift, equal to the original measures and carrying the same
uniform mass and unit-support bounds eventually. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (C : ℝ≥0∞)
    (hC : C < ⊤)
    (hmass : ∀ᶠ i in l, (μi i) Set.univ ≤ C)
    (hunit : ∀ᶠ i in l, ∀ᵐ z ∂μi i, z ∈ Set.Icc (0 : ℝ) 1) :
    ∃ νi : ι → FiniteMeasure ℝ,
      ∀ᶠ i in l,
        (νi i : Measure ℝ) = μi i ∧
        (νi i).mass ≤ C.toNNReal ∧
        (νi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  classical
  let νi : ι → FiniteMeasure ℝ := fun i =>
    if h : (μi i) Set.univ < ⊤ then
      ⟨μi i, (isFiniteMeasure_iff (μi i)).2 h⟩
    else 0
  refine ⟨νi, ?_⟩
  filter_upwards [hmass, hunit] with i hm hu
  have hf : (μi i) Set.univ < ⊤ := lt_of_le_of_lt hm hC
  have hzero : (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    (mem_ae_iff).1 hu
  have hμ : (νi i : Measure ℝ) = μi i := by
    simpa [νi, hf]
  have hbound : (νi i).mass ≤ C.toNNReal := by
    apply (ENNReal.coe_le_coe).1
    rw [FiniteMeasure.ennreal_mass, hμ, ENNReal.coe_toNNReal hC.ne]
    exact hm
  refine ⟨hμ, hbound, ?_⟩
  exact (FiniteMeasure.null_iff_toMeasure_null (νi i) _).2
    (by simpa [hμ] using hzero)
