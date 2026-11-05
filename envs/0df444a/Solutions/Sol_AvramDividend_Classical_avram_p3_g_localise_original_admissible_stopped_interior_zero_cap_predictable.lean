-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:13:18.454608+00:00
-- url     : https://prove2.me/submissions/21cf2353-7cce-415a-9e65-1243f26af451

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_prestate_predictable_zero_interior_cap_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All three actual pre-reserve regimes remain predictable after the
original finite ruin stop, including the stopping instant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    (∀ ω, τ ω ≤ T) ∧
    IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧ Z p = 0} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        ENNReal.ofReal (Z p) = C} := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hClock := avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
    X x D hStrategy T
  have hMasks :=
    avram_p3_g_localise_original_prestate_predictable_zero_interior_cap_partition
      X x D hStrategy C
  rcases hMasks with ⟨hZero, hCap, hInterior, _hPartition⟩
  have hPred := avram_wave3_04_inclusiveSurvival_stronglyPredictable
    (fun ω : Ω => (τ ω : ℝ≥0∞)) hClock.2
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hM : Measurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) then (1 : ℝ) else 0) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) then (1 : ℝ) else 0)
      from hPred).measurable
  have hSurvive : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} := by
    have hEq : ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} : Set (ℝ≥0 × Ω)) =
        (fun p : ℝ≥0 × Ω =>
          if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) then (1 : ℝ) else 0) ⁻¹'
          ({1} : Set ℝ) := by
      ext p
      simp
    rw [hEq]
    exact (measurableSet_singleton (1 : ℝ)).preimage hM
  refine ⟨hClock.1, hClock.2, ?_, ?_, ?_⟩
  · change MeasurableSet[𝓕.rightCont.predictable]
      ({p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} ∩
       {p : ℝ≥0 × Ω | 0 < Z p ∧ ENNReal.ofReal (Z p) < C})
    exact hSurvive.inter hInterior
  · change MeasurableSet[𝓕.rightCont.predictable]
      ({p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} ∩
       {p : ℝ≥0 × Ω | Z p = 0})
    exact hSurvive.inter hZero
  · change MeasurableSet[𝓕.rightCont.predictable]
      ({p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} ∩
       {p : ℝ≥0 × Ω | ENNReal.ofReal (Z p) = C})
    exact hSurvive.inter hCap
