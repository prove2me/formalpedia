-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_phys58_original_fullmask_discount_marked_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:54:30.329207+00:00
-- url     : https://prove2.me/submissions/ec2ef689-f5f2-4e20-806f-d9c0f571cb6c

import Mathlib
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

/-- The original finite-cap stopped discount factor is marked-predictable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
           (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
           0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) else 0) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  change ∀ n, Measurable[(𝓕.rightCont.predictable).prod
    (inferInstance : MeasurableSpace ℝ)]
    (fun p : (ℝ≥0 × Ω) × ℝ =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) else 0)
  have hpredict := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    X x D hD.1.1
  have hτ := ruinTime_stopping_rightCont_filtration X x D hD.1.1
  have hsurv := avram_wave3_04_inclusiveSurvival_stronglyPredictable
    (𝓕 := 𝓕.rightCont) (ruinTime X x D) hτ
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hmU : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω => U p.1 p.2) from hpredict).measurable
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
  have hExp : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => Real.exp (-(q * (p.1.1 : ℝ)))) :=
    Real.measurable_exp.comp ((measurable_const.mul
      (hmt.coe_nnreal_real.comp measurable_fst)).neg)
  intro n
  let E : Set (ℝ≥0 × Ω) := {p |
    0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
    (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
    0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
  have hEm : MeasurableSet E := by
    have h0 : MeasurableSet {p : ℝ≥0 × Ω | 0 < p.1} :=
      (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ≥0))).preimage hmt
    have hT' : MeasurableSet {p : ℝ≥0 × Ω | (p.1 : ℝ) < T - δ n} :=
      measurableSet_Iio.preimage (hmt.coe_nnreal_real)
    have hU0 : MeasurableSet {p : ℝ≥0 × Ω | 0 ≤ U p.1 p.2} :=
      measurableSet_Ici.preimage hmU
    have hUC : MeasurableSet {p : ℝ≥0 × Ω |
        ENNReal.ofReal (U p.1 p.2) ≤ C} :=
      measurableSet_Iic.preimage (hmU.ennreal_ofReal)
    simpa [E, Set.setOf_and, Set.inter_assoc] using
      ((((h0.inter hT').inter hSurvSet).inter hU0).inter hUC)
  have hCondition : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ | p.1 ∈ E ∧ p.2 < 0} := by
    have hFirst : MeasurableSet[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
        {p : (ℝ≥0 × Ω) × ℝ | p.1 ∈ E} :=
      hEm.preimage measurable_fst
    have hSecond : MeasurableSet[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
        {p : (ℝ≥0 × Ω) × ℝ | p.2 < 0} :=
      (measurableSet_Iio : MeasurableSet (Iio (0 : ℝ))).preimage measurable_snd
    exact hFirst.inter hSecond
  have hMasked : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if p.1 ∈ E ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) else 0) :=
    Measurable.ite hCondition hExp measurable_const
  simpa only [E, Set.mem_setOf_eq, and_assoc] using hMasked
