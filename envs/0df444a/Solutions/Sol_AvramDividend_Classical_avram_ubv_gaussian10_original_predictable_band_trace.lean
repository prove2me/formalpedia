-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_band_trace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:38:45.203511+00:00
-- url     : https://prove2.me/submissions/d7750da7-61e3-42f3-93b1-d33c00a0f9ff

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A predictable set remains measurable in Borel time times the original
filtration when restricted to a finite time band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ≥0)
    (S : Set (ℝ≥0 × Ω))
    (hS : MeasurableSet[𝓕.predictable] S) :
    MeasurableSet[@Prod.instMeasurableSpace ℝ≥0 Ω inferInstance (𝓕 b)]
      (S ∩ (Ioc a b ×ˢ (univ : Set Ω))) := by
  let mBand : MeasurableSpace (ℝ≥0 × Ω) :=
    @Prod.instMeasurableSpace ℝ≥0 Ω inferInstance (𝓕 b)
  let band : Set (ℝ≥0 × Ω) := Ioc a b ×ˢ (univ : Set Ω)
  have hband : MeasurableSet[mBand] band :=
    measurableSet_Ioc.prod (@MeasurableSet.univ Ω (𝓕 b))
  let mTrace : MeasurableSpace (ℝ≥0 × Ω) :=
    { MeasurableSet' := fun A => MeasurableSet[mBand] (A ∩ band)
      measurableSet_empty := by
        change MeasurableSet[mBand] (∅ ∩ band)
        rw [Set.empty_inter]
        exact @MeasurableSet.empty _ mBand
      measurableSet_compl := by
        intro A hA
        change MeasurableSet[mBand] (Aᶜ ∩ band)
        rw [show Aᶜ ∩ band = band \ (A ∩ band) from by
          ext z; simp only [Set.mem_inter_iff, Set.mem_compl_iff,
            Set.mem_sdiff]; tauto]
        exact hband.diff hA
      measurableSet_iUnion := by
        intro f hf
        change MeasurableSet[mBand] ((⋃ i, f i) ∩ band)
        rw [Set.iUnion_inter]
        exact MeasurableSet.iUnion hf }
  have hle : 𝓕.predictable ≤ mTrace := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      change MeasurableSet[mBand] (({(0 : ℝ≥0)} ×ˢ A) ∩ band)
      rw [Set.prod_inter_prod]
      have hzero : ({(0 : ℝ≥0)} ∩ Ioc a b : Set ℝ≥0) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ a from bot_le)) (ht.1 ▸ ht.2.1)
      rw [hzero, Set.empty_prod]
      exact @MeasurableSet.empty _ mBand
    · intro i A hA
      change MeasurableSet[mBand] ((Ioi i ×ˢ A) ∩ band)
      rw [Set.prod_inter_prod, Set.inter_univ]
      by_cases hib : i ≤ b
      · exact (measurableSet_Ioi.inter measurableSet_Ioc).prod (𝓕.mono hib A hA)
      · have hbi : b < i := lt_of_not_ge hib
        have hempty : (Ioi i ∩ Ioc a b : Set ℝ≥0) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact (not_le_of_gt hbi) ((le_of_lt ht.1).trans ht.2.2)
        rw [hempty, Set.empty_prod]
        exact @MeasurableSet.empty _ mBand
  exact hle S hS
