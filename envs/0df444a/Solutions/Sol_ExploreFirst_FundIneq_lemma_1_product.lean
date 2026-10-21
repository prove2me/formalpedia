-- Prove2me | solution 1 for ExploreFirst.FundIneq.lemma_1_product
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:43:05.351205+00:00
-- url     : https://prove2.me/submissions/8832dd97-5f8e-4e94-a711-420a51097dcc

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory unitInterval
open scoped ENNReal

theorem solution {Γ : Type*} [MeasurableSpace Γ] (P₁ P₂ : Measure Γ)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    klDiv P₁ P₂ =
      klDiv (P₁.prod (volume : Measure unitInterval)) (P₂.prod (volume : Measure unitInterval)) := by
  apply le_antisymm
  · have h := klDiv_map_le (μ := P₁.prod (volume : Measure unitInterval))
      (ν := P₂.prod (volume : Measure unitInterval)) (g := Prod.fst) measurable_fst
    simpa using h
  · rw [← Measure.compProd_const, ← Measure.compProd_const]
    exact (klDiv_compProd_left (μ := P₁) (ν := P₂)
      (κ := Kernel.const Γ (volume : Measure unitInterval))).le
