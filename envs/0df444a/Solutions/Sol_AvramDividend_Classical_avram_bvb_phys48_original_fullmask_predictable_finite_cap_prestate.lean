-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:05:22.337361+00:00
-- url     : https://prove2.me/submissions/3339463f-871a-4a12-ae0c-85efcdf08bcf

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

/-- The source-exact stopped prestate mask is predictable and bounded by its finite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    ∀ n : ℕ,
      let E : Set (ℝ≥0 × Ω) := {p |
        0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
      MeasurableSet[𝓕.rightCont.predictable] E ∧
        ∀ p ∈ E, U p.1 p.2 ≤ C.toReal := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  change ∀ n : ℕ,
    let E : Set (ℝ≥0 × Ω) := {p |
      0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
      (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
      0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
    MeasurableSet[𝓕.rightCont.predictable] E ∧
      ∀ p ∈ E, U p.1 p.2 ≤ C.toReal
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
  intro n
  let E : Set (ℝ≥0 × Ω) := {p |
    0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
    (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
    0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
  change MeasurableSet E ∧ ∀ p ∈ E, U p.1 p.2 ≤ C.toReal
  constructor
  · have h0 : MeasurableSet {p : ℝ≥0 × Ω | 0 < p.1} :=
      (show MeasurableSet (Set.Ioi (0 : ℝ≥0)) from measurableSet_Ioi).preimage hmt
    have hmtReal : Measurable (fun p : ℝ≥0 × Ω => (p.1 : ℝ)) := by
      exact (show Measurable (fun t : ℝ≥0 => (t : ℝ)) from
        measurable_subtype_coe).comp hmt
    have hT' : MeasurableSet {p : ℝ≥0 × Ω | (p.1 : ℝ) < T - δ n} :=
      measurableSet_Iio.preimage hmtReal
    have hU0 : MeasurableSet {p : ℝ≥0 × Ω | 0 ≤ U p.1 p.2} :=
      measurableSet_Ici.preimage hmU
    have hUC : MeasurableSet {p : ℝ≥0 × Ω |
        ENNReal.ofReal (U p.1 p.2) ≤ C} :=
      measurableSet_Iic.preimage (hmU.ennreal_ofReal)
    change MeasurableSet {p : ℝ≥0 × Ω |
      0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
      (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
      0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
    simpa [Set.setOf_and, Set.inter_assoc] using
      ((((h0.inter hT').inter hSurvSet).inter hU0).inter hUC)
  · intro p hp
    have hp0 : 0 ≤ U p.1 p.2 := hp.2.2.2.1
    have hpC : ENNReal.ofReal (U p.1 p.2) ≤ C := hp.2.2.2.2
    have h := ENNReal.toReal_mono hFinite hpC
    simpa only [ENNReal.toReal_ofReal hp0] using h
