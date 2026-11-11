-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys58_original_fullmask_discount_marked_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:53:38.705413+00:00
-- url     : https://prove2.me/submissions/32da5147-aa97-4ae2-acab-45d7ee9a841b

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A discounted indicator of the original predictable stopped jump mask is marked-predictable. -/
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
  change ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
    (fun p : (ℝ≥0 × Ω) × ℝ =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) else 0)
  have hMask := avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate
    X x D C hC hFinite hD T hT
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hmt : Measurable (fun p : ℝ≥0 × Ω => p.1) := by
    apply measurable_of_Ioi
    intro a
    have h := measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
      (i := a) (s := (Set.univ : Set Ω)) MeasurableSet.univ
    simpa only [Set.preimage, Set.Ioi, Set.prod_univ, Set.mem_setOf_eq] using h
  have hmTime : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => (p.1.1 : ℝ)) :=
    (measurable_subtype_coe.comp hmt).comp measurable_fst
  have hmExp : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      Real.exp (-(q * (p.1.1 : ℝ)))) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul hmTime).neg
  have hmNeg : MeasurableSet {p : (ℝ≥0 × Ω) × ℝ | p.2 < 0} :=
    measurableSet_Iio.preimage measurable_snd
  intro n
  have hE : MeasurableSet {p : ℝ≥0 × Ω |
      0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
      (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
      0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C} :=
    (hMask n).1
  have hGate : MeasurableSet {p : (ℝ≥0 × Ω) × ℝ |
      0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
      (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
      0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0} := by
    have hJoint := (hE.preimage measurable_fst).inter hmNeg
    convert hJoint using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  exact hmExp.ite hGate measurable_const
