-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja23_integral_Ioo_split_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:07:45.998963+00:00
-- url     : https://prove2.me/submissions/9e1231ae-8f05-4bf9-8e61-7a176bf5f9ce

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- The finite annulus and remaining open tail partition the real quadratic energy. -/
theorem solution
    (μ : Measure ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hbc : b < c)
    (hI : IntegrableOn (fun z : ℝ => z ^ 2) (Ioo a c) μ) :
    (∫ z in Ioo a c, z ^ 2 ∂μ) =
      (∫ z in Ioc a b, z ^ 2 ∂μ) +
      (∫ z in Ioo b c, z ^ 2 ∂μ) := by
  have hA : Ioc a b ⊆ Ioo a c := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hbc⟩
  have hB : Ioo b c ⊆ Ioo a c := by
    intro z hz
    exact ⟨lt_of_le_of_lt hab hz.1, hz.2⟩
  have hDisj : Disjoint (Ioc a b) (Ioo b c) := by
    apply disjoint_left.mpr
    intro z hzA hzB
    exact (not_lt_of_ge hzA.2) hzB.1
  have hSplit := MeasureTheory.setIntegral_union hDisj
    measurableSet_Ioo (hI.mono_set hA) (hI.mono_set hB)
  simpa only [Set.Ioc_union_Ioo_eq_Ioo hab hbc] using hSplit
