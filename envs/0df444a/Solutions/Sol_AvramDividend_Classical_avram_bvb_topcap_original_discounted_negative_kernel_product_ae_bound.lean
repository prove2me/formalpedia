-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:27:38.884697+00:00
-- url     : https://prove2.me/submissions/f15775fc-d3db-47f0-b15c-4b45955def8d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_ae_bound_transfer_equal_predictable_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original top-cap predictable product-a.e. mark bound via the physical clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ⊤)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ∀ᵐ p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))),
          |H n p| ≤ K) := by
  intro δ U H
  letI : IsProbabilityMeasure P := X.isProbability
  have hPred := AvramDividend.Classical.avram_bvb_topcap_original_marked_predictable
    X hBV q hq w C hC hCapTop hw_cont hw_neg x D hD T hT hActivity
  obtain ⟨K, hK, hReward⟩ :=
    AvramDividend.Classical.avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
      X hBV q hq w hw_cont hw_neg x D hD.1.1 (Real.toNNReal T)
  have hPredLe : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      have hA' : MeasurableSet A := (𝓕.rightCont.le (⊥ : ℝ≥0)) A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod hA'
    · intro i A hA
      have hA' : MeasurableSet A := (𝓕.rightCont.le i) A hA
      exact (measurableSet_Ioi : MeasurableSet (Ioi i)).prod hA'
  have hPredSection (n : ℕ) (z : ℝ) :
      Measurable[𝓕.rightCont.predictable]
        (fun p : ℝ≥0 × Ω => H n (p, z)) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    have hMap : Measurable (fun p : ℝ≥0 × Ω => (p, z)) := by fun_prop
    exact (hPred n).comp hMap
  have hOrdSection (n : ℕ) (z : ℝ) :
      Measurable (fun p : ℝ≥0 × Ω => H n (p, z)) :=
    (hPredSection n z).mono hPredLe le_rfl
  have hδ (n : ℕ) : 0 ≤ δ n := div_nonneg hT.le (by positivity)
  have hAtTime (n : ℕ) (z : ℝ) (t : ℝ≥0) :
      ∀ᵐ ω ∂P, |H n ((t, ω), z)| ≤ K := by
    filter_upwards [hReward] with ω hω
    by_cases hmask :
        0 < t ∧ (t : ℝ) < T - δ n ∧
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C ∧ z < 0
    · have ht : (t : ℝ) ≤ T :=
        le_of_lt (lt_of_lt_of_le hmask.2.1 (sub_le_self T (hδ n)))
      have htNN : t ≤ Real.toNNReal T := by
        have htReal : (t : ℝ) ≤ (Real.toNNReal T : ℝ) := by
          simpa only [Real.coe_toNNReal T hT.le] using ht
        exact_mod_cast htReal
      have hPoint := hω t htNN hmask.2.2.2.1 z hmask.2.2.2.2.2
      simpa only [H, U, if_pos hmask] using hPoint
    · simpa only [H, if_neg hmask, abs_zero] using hK
  have hOrdAE (n : ℕ) (z : ℝ) :
      ∀ᵐ p ∂((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal).prod P), |H n (p, z)| ≤ K := by
    have hSet : MeasurableSet {p : ℝ≥0 × Ω | |H n (p, z)| ≤ K} :=
      measurableSet_Iic.preimage (hOrdSection n z).abs
    exact (Measure.ae_prod_iff_ae_ae hSet).2
      (Filter.Eventually.of_forall (fun t => hAtTime n z t))
  have hμAE (n : ℕ) (z : ℝ) :
      ∀ᵐ p ∂μ, |H n (p, z)| ≤ K :=
    AvramDividend.Classical.avram_bvb_topcap_ae_bound_transfer_equal_predictable_measure
      𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω))
      μ ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal).prod P)
      hμclock (fun p => H n (p, z)) (hPredSection n z) K (hOrdAE n z)
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hνfinite : ν Set.univ < ⊤ := by simpa [ν] using hActivity
  letI : IsFiniteMeasure μ := ⟨hμfinite⟩
  letI : IsFiniteMeasure ν := ⟨hνfinite⟩
  refine ⟨K, hK, ?_⟩
  intro n
  have hm : MeasurableSet
      {p : (ℝ≥0 × Ω) × ℝ | |H n p| ≤ K} :=
    measurableSet_Iic.preimage (hPred n).abs
  have hSwap : ∀ᵐ p ∂μ, ∀ᵐ z ∂ν, |H n (p, z)| ≤ K :=
    (Measure.ae_ae_comm hm).2
      (Filter.Eventually.of_forall (fun z => hμAE n z))
  exact (Measure.ae_prod_iff_ae_ae hm).2 hSwap
