-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Icc_identity_of_Ioc_and_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:47:44.429055+00:00
-- url     : https://prove2.me/submissions/3ff07aaf-d663-42d6-a0fa-b41db2496dbe

import Mathlib.Topology.EMetricSpace.BoundedVariation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Icc_Ioc_endpoint_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The closed Stieltjes product rule follows from a half-open rule when
the discount has no left endpoint atom and all four interval pieces are
integrable. This does not assert the missing half-open product rule. -/
theorem solution
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hfa : Function.leftLim f a = Function.rightLim f a)
    (hflIoc : hg.vectorMeasure.IntegrableOn (Function.leftLim f) (Ioc a b))
    (hflAt : hg.vectorMeasure.IntegrableOn (Function.leftLim f) ({a} : Set ℝ≥0))
    (hgrIoc : hf.vectorMeasure.IntegrableOn (Function.rightLim g) (Ioc a b))
    (hgrAt : hf.vectorMeasure.IntegrableOn (Function.rightLim g) ({a} : Set ℝ≥0))
    (hIoc :
      (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
        Function.rightLim f b • Function.rightLim g b -
        Function.rightLim f a • Function.rightLim g a -
        (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure)) :
    (∫ᵛ t in Icc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
      Function.rightLim f b • Function.rightLim g b -
      Function.leftLim f a • Function.leftLim g a -
      (∫ᵛ t in Icc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by
  obtain ⟨hLeft, hRight⟩ :=
    avram_wave6_05_generic_bv_stieltjes_Icc_Ioc_endpoint_split
      f g hf hg a b hab hflIoc hflAt hgrIoc hgrAt
  rw [hLeft, hRight, hIoc, hfa]
  simp only [sub_self, zero_smul, add_zero, smul_eq_mul]
  ring
