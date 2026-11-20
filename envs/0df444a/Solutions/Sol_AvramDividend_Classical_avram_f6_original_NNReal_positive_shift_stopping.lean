-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_NNReal_positive_shift_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:11:40.811211+00:00
-- url     : https://prove2.me/submissions/44dbc075-5f55-4359-b17c-ce0770c0a2b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (δ : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  by_cases ht : δ ≤ t
  · have heq : {ω : Ω | ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω : Ω | (σ ω : WithTop ℝ≥0) ≤ (t - δ : ℝ≥0)} := by
      ext ω
      simp only [mem_setOf_eq, WithTop.coe_le_coe]
      exact (le_tsub_iff_right ht).symm
    rw [heq]
    exact (𝓕.rightCont.mono (tsub_le_self : t - δ ≤ t)) _
      (hσ (t - δ))
  · have heq : {ω : Ω | ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false,
        WithTop.coe_le_coe]
      intro hh
      exact ht ((le_add_of_nonneg_left (σ ω).property).trans hh)
    rw [heq]
    exact (@MeasurableSet.empty Ω ((𝓕.rightCont) t))
