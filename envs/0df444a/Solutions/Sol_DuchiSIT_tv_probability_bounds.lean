-- Prove2me | solution 1 for DuchiSIT.tv_probability_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T18:21:36.873477+00:00
-- url     : https://prove2.me/submissions/504258fd-13cd-460a-8df2-a9a4511ae5a8

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory



theorem solution {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ A : Set X, MeasurableSet A → |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν) ∧
    0 ≤ MarkovChainCLT.tvDist μ ν ∧ MarkovChainCLT.tvDist μ ν ≤ 1 ∧
    (MarkovChainCLT.tvDist μ ν = 0 ↔ μ = ν) := by
  classical
  have hreal (ρ : Measure X) [IsProbabilityMeasure ρ] (A : Set X) :
      0 ≤ (ρ A).toReal ∧ (ρ A).toReal ≤ 1 :=
    ⟨ENNReal.toReal_nonneg,
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one (μ := ρ) (s := A)))⟩
  have habs (A : Set X) : |(μ A).toReal - (ν A).toReal| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(hreal μ A).1, (hreal μ A).2, (hreal ν A).1, (hreal ν A).2]
  have hbdd : BddAbove {r : ℝ | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    exact habs A
  have hevent (A : Set X) (hA : MeasurableSet A) :
      |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν :=
    le_csSup hbdd ⟨A, hA, rfl⟩
  have h0 : 0 ≤ MarkovChainCLT.tvDist μ ν := by
    simpa using hevent ∅ MeasurableSet.empty
  have h1 : MarkovChainCLT.tvDist μ ν ≤ 1 := by
    apply Real.sSup_le _ zero_le_one
    rintro r ⟨A, hA, rfl⟩
    exact habs A
  refine ⟨hevent, h0, h1, ?_⟩
  constructor
  · intro hz
    apply Measure.ext
    intro A hA
    have h := hevent A hA
    rw [hz] at h
    have heq : (μ A).toReal = (ν A).toReal := sub_eq_zero.mp (abs_nonpos_iff.mp h)
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp heq
  · intro heq
    subst ν
    apply le_antisymm _ h0
    apply Real.sSup_le _ le_rfl
    rintro r ⟨A, hA, rfl⟩
    simp
