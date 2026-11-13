-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_fullmask_predictable_prestate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:35:49.230361+00:00
-- url     : https://prove2.me/submissions/8301d699-d24e-45ec-ba38-68e16a3f3e5e

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
    (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
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
      MeasurableSet[𝓕.rightCont.predictable] E := by
  intro δ U
  have hpredict := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    X x D hD.1.1
  have hτ := ruinTime_stopping_rightCont_filtration X x D hD.1.1
  have hsurv := avram_wave3_04_inclusiveSurvival_stronglyPredictable
    (𝓕 := 𝓕.rightCont) (ruinTime X x D) hτ
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hmU : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2) :=
    hpredict.measurable
  have hmt : Measurable (fun p : ℝ≥0 × Ω => p.1) := by
    apply measurable_of_Ioi
    intro a
    simpa only [Set.preimage, Set.Ioi, Set.prod_univ, Set.mem_setOf_eq] using
      (measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
        (i := a) (s := (Set.univ : Set Ω)) MeasurableSet.univ)
  have hSurv : MeasurableSet {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2} := by
    have h := (show Measurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
      from hsurv.measurable)
    convert (measurableSet_singleton (1 : ℝ)).preimage h using 1
    ext p
    by_cases hp : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 <;> simp [hp]
  intro n
  change MeasurableSet {p : ℝ≥0 × Ω |
    0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
    (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
    0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
  have ha : MeasurableSet {p : ℝ≥0 × Ω | 0 < p.1} :=
    measurableSet_lt measurable_const hmt
  have hb : MeasurableSet {p : ℝ≥0 × Ω |
      (p.1 : ℝ) < T - δ n} :=
    measurableSet_Iio.preimage (measurable_coe_nnreal_real.comp hmt)
  have hc : MeasurableSet {p : ℝ≥0 × Ω | 0 ≤ U p.1 p.2} :=
    measurableSet_Ici.preimage hmU
  have hd : MeasurableSet {p : ℝ≥0 × Ω |
      ENNReal.ofReal (U p.1 p.2) ≤ C} :=
    measurableSet_Iic.preimage hmU.ennreal_ofReal
  simpa [Set.setOf_and, Set.inter_assoc] using
    ((((ha.inter hb).inter hSurv).inter hc).inter hd)
