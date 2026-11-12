-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja23_integral_cutoff_tendsto_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:12:54.812516+00:00
-- url     : https://prove2.me/submissions/649aeff3-8d55-40a4-8af6-98930517e645

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- The quadratic strip energy approaches the full open-tail energy. -/
theorem solution
    (μ : Measure ℝ) (a : ℝ) (b : ℕ → ℝ)
    (hOrder : ∀ᶠ m in atTop, a ≤ b m ∧ b m < 0)
    (hI : IntegrableOn (fun z : ℝ => z ^ 2) (Ioo a 0) μ)
    (hTail : Tendsto
      (fun m : ℕ => ∫ z in Ioo (b m) 0, z ^ 2 ∂μ)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun m : ℕ => ∫ z in Ioc a (b m), z ^ 2 ∂μ)
      atTop (nhds (∫ z in Ioo a 0, z ^ 2 ∂μ)) := by
  have hEq : ∀ᶠ m in atTop,
      (∫ z in Ioc a (b m), z ^ 2 ∂μ) =
        (∫ z in Ioo a 0, z ^ 2 ∂μ) -
          (∫ z in Ioo (b m) 0, z ^ 2 ∂μ) := by
    filter_upwards [hOrder] with m hm
    have hA : Ioc a (b m) ⊆ Ioo a 0 := by
      intro z hz
      exact ⟨hz.1, lt_of_le_of_lt hz.2 hm.2⟩
    have hB : Ioo (b m) 0 ⊆ Ioo a 0 := by
      intro z hz
      exact ⟨lt_of_le_of_lt hm.1 hz.1, hz.2⟩
    have hDisj : Disjoint (Ioc a (b m)) (Ioo (b m) 0) := by
      apply disjoint_left.mpr
      intro z hzA hzB
      exact (not_lt_of_ge hzA.2) hzB.1
    have hSplit := MeasureTheory.setIntegral_union hDisj
      measurableSet_Ioo (hI.mono_set hA) (hI.mono_set hB)
    have hs :
        (∫ z in Ioo a 0, z ^ 2 ∂μ) =
          (∫ z in Ioc a (b m), z ^ 2 ∂μ) +
          (∫ z in Ioo (b m) 0, z ^ 2 ∂μ) := by
      simpa only [Set.Ioc_union_Ioo_eq_Ioo hm.1 hm.2] using hSplit
    linarith
  have hSub : Tendsto
      (fun m : ℕ => (∫ z in Ioo a 0, z ^ 2 ∂μ) -
        (∫ z in Ioo (b m) 0, z ^ 2 ∂μ))
      atTop
      (nhds ((∫ z in Ioo a 0, z ^ 2 ∂μ) - (0 : ℝ))) :=
    tendsto_const_nhds.sub hTail
  have hEqSymm : ∀ᶠ m in atTop,
      (∫ z in Ioo a 0, z ^ 2 ∂μ) -
          (∫ z in Ioo (b m) 0, z ^ 2 ∂μ) =
        (∫ z in Ioc a (b m), z ^ 2 ∂μ) := by
    filter_upwards [hEq] with m hm
    exact hm.symm
  simpa using hSub.congr' hEqSymm
