-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:41:45.887974+00:00
-- url     : https://prove2.me/submissions/4cc5f1b8-933d-40e2-8aef-600a9048cb6d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- A Bochner integral is the sum of its integrals over the exact cells of a measurable natural-valued count. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (hF : Integrable F P) :
    HasSum (fun k : ℕ => ∫ ω in {ω : Ω | K ω = k}, F ω ∂P)
      (∫ ω, F ω ∂P) := by
  have hM : ∀ k : ℕ, MeasurableSet {ω : Ω | K ω = k} := by
    intro k
    exact hK (measurableSet_singleton k)
  have hD : Pairwise
      (fun i j : ℕ => Disjoint {ω : Ω | K ω = i}
        {ω : Ω | K ω = j}) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (hi.symm.trans hj)
  have hU : (⋃ k : ℕ, {ω : Ω | K ω = k}) = Set.univ := by
    ext ω
    simp
  have hInt : IntegrableOn F (⋃ k : ℕ, {ω : Ω | K ω = k}) P := by
    simpa [hU] using hF
  simpa [hU] using
    (MeasureTheory.hasSum_integral_iUnion hM hD hInt)
