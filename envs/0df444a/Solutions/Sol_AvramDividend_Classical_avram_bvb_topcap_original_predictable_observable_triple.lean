-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_predictable_observable_triple
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:01:34.159035+00:00
-- url     : https://prove2.me/submissions/d1ed3ff8-5541-46f3-992f-4f4d391b74bd

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    let U : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    Measurable[𝓕.rightCont.predictable] U ∧
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω => p.1) ∧
    MeasurableSet[𝓕.rightCont.predictable] {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2} := by
  let U : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hpredict := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    X x D hD
  have hτ := ruinTime_stopping_rightCont_filtration X x D hD
  have hsurv := avram_wave3_04_inclusiveSurvival_stronglyPredictable
    (𝓕 := 𝓕.rightCont) (ruinTime X x D) hτ
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hmU : Measurable (fun p : ℝ≥0 × Ω => U p) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω => U p) from hpredict).measurable
  have hmt : Measurable (fun p : ℝ≥0 × Ω => p.1) := by
    apply measurable_of_Ioi
    intro a
    have h := measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
      (i := a) (s := (Set.univ : Set Ω)) MeasurableSet.univ
    simpa only [Set.preimage, Set.Ioi, Set.prod_univ, Set.mem_setOf_eq] using h
  have hmSurv : Measurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
      from hsurv).measurable
  have hSurvSet : MeasurableSet {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2} := by
    have hs := (measurableSet_singleton (1 : ℝ)).preimage hmSurv
    convert hs using 1
    ext p
    by_cases h : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 <;> simp [h]
  exact ⟨hmU, hmt, hSurvSet⟩
