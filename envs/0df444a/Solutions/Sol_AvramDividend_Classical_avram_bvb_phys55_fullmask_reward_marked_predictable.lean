-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys55_fullmask_reward_marked_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:52:15.575742+00:00
-- url     : https://prove2.me/submissions/2c328c74-d14a-4d07-9661-13446d6c92ac

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original bounded-reserve marked dividend reward is predictable jointly in time and mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (H n) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
    if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
       (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
       0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
  change ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (H n)
  have hMask := avram_bvb_phys48_original_fullmask_predictable_finite_cap_prestate
    X x D C hC hFinite hD T hT
  -- Use the source process's right-continuous filtration for the original prestate.
  have hpredict := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    X x D hD.1.1
  have hwMeas : Measurable w :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w w ⊤ hw_cont (fun y hy => hw_neg y hy)
      (by intro _ y; rfl) (by intro h; exact False.elim (h rfl))
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hmU : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω => U p.1 p.2) from
      hpredict).measurable
  have hmt : Measurable (fun p : ℝ≥0 × Ω => p.1) := by
    apply measurable_of_Ioi
    intro a
    have h := measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
      (i := a) (s := (Set.univ : Set Ω)) MeasurableSet.univ
    simpa only [Set.preimage, Set.Ioi, Set.prod_univ, Set.mem_setOf_eq] using h
  have hmTime : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => (p.1.1 : ℝ)) :=
    (measurable_subtype_coe.comp hmt).comp measurable_fst
  have hmReserve : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => U p.1.1 p.1.2) :=
    hmU.comp measurable_fst
  have hmMark : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => p.2) :=
    measurable_snd
  have hmReward : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2))) := by
    have hExp : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
        Real.exp (-(q * (p.1.1 : ℝ)))) :=
      Real.continuous_exp.measurable.comp (measurable_const.mul hmTime).neg
    exact hExp.mul ((hwMeas.comp (hmReserve.add hmMark)).sub
      (hwMeas.comp hmReserve))
  have hmNeg : MeasurableSet {p : (ℝ≥0 × Ω) × ℝ | p.2 < 0} :=
    measurableSet_Iio.preimage hmMark
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
  change Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
    if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
       (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
       0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0)
  exact hmReward.ite hGate measurable_const
