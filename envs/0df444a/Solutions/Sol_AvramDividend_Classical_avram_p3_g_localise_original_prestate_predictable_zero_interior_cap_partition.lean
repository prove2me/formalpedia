-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_prestate_predictable_zero_interior_cap_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:47:06.270368+00:00
-- url     : https://prove2.me/submissions/ff6460e9-f3b0-4efa-bacf-e92977146c91

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual pre-reserve has measurable zero, strict-cap interior, and
cap-contact regions. No boundary occupation is asserted to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) :
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable] {p | Z p = 0} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | ENNReal.ofReal (Z p) = C} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | 0 < Z p ∧ ENNReal.ofReal (Z p) < C} ∧
    ∀ p, 0 ≤ Z p → ENNReal.ofReal (Z p) ≤ C →
      Z p = 0 ∨ (0 < Z p ∧ ENNReal.ofReal (Z p) < C) ∨
        ENNReal.ofReal (Z p) = C := by
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hPred := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    X x D hD
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hm : Measurable Z :=
    (show StronglyMeasurable Z from hPred).measurable
  have hmc : Measurable (fun p => ENNReal.ofReal (Z p)) :=
    ENNReal.continuous_ofReal.measurable.comp hm
  have hzero : MeasurableSet[𝓕.rightCont.predictable] {p | Z p = 0} :=
    (measurableSet_singleton (0 : ℝ)).preimage hm
  have hcap : MeasurableSet[𝓕.rightCont.predictable]
      {p | ENNReal.ofReal (Z p) = C} :=
    (measurableSet_singleton C).preimage hmc
  have hpos : MeasurableSet[𝓕.rightCont.predictable] {p | 0 < Z p} :=
    isOpen_Ioi.measurableSet.preimage hm
  have hbelow : MeasurableSet[𝓕.rightCont.predictable]
      {p | ENNReal.ofReal (Z p) < C} :=
    isOpen_Iio.measurableSet.preimage hmc
  have hinterior : MeasurableSet[𝓕.rightCont.predictable]
      {p | 0 < Z p ∧ ENNReal.ofReal (Z p) < C} := by
    change MeasurableSet[𝓕.rightCont.predictable]
      ({p | 0 < Z p} ∩ {p | ENNReal.ofReal (Z p) < C})
    exact hpos.inter hbelow
  refine ⟨hzero, hcap, hinterior, ?_⟩
  intro p hp hc
  by_cases hz : Z p = 0
  · exact Or.inl hz
  have hp' : 0 < Z p := lt_of_le_of_ne hp (Ne.symm hz)
  by_cases hc' : ENNReal.ofReal (Z p) = C
  · exact Or.inr (Or.inr hc')
  exact Or.inr (Or.inl ⟨hp', lt_of_le_of_ne hc hc'⟩)
