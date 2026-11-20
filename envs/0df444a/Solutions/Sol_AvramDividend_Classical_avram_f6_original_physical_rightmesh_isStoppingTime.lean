-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_physical_rightmesh_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:44:02.339746+00:00
-- url     : https://prove2.me/submissions/e6a3da24-7915-4dfa-b375-09e61a90f017

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_NNReal_positive_shift_stopping
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ σ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (δ : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (τ ω) (σ ω + δ) : ℝ≥0) : WithTop ℝ≥0)) := by
  have hshift :=
    avram_f6_original_NNReal_positive_shift_stopping σ hσ δ
  simpa only [WithTop.coe_min] using hτ.min hshift
