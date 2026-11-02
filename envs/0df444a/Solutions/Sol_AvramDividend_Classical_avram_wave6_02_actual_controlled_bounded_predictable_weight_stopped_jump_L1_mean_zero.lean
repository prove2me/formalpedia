-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_controlled_bounded_predictable_weight_stopped_jump_L1_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:51:10.365656+00:00
-- url     : https://prove2.me/submissions/01812863-09e5-4764-b54b-f6194e8c3777

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_physical_clock_rightcont_stopped_compensated_L1_no_initial_rectangle
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
  :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀     (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (a : (ℝ≥0 × Ω) → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (Mbound : ℝ) (haBound : ∀ p, |a p| ≤ Mbound)
    (haSupport : ∀ p : ℝ≥0 × Ω, T < p.1 → a p = 0),
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    Integrable (fun ω =>
      (∫ p, GW ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, GW p ∂N)) P ∧
    (∫ ω, ((∫ p, GW ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ p, GW p ∂N)) ∂P) = 0 := by
  classical
  intro NX K M hM T S hST MT N hMT μ hμ hμclock hN
    B hBm hBmono hBcover hLocal hFuture
    a ha Mbound haBound haSupport Y J HS GW
  obtain ⟨hHSm, _, _⟩ :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  have hGWi :=
    (avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ a ha Mbound haBound).1
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have haLift : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1) :=
    ha.comp measurable_fst
  have hGWm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] GW := by
    exact haLift.mul hHSm
  have hGiN : Integrable GW N := by
    rw [hN]
    exact hGWi
  have hStop : GW = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then GW p else 0 := by
    funext p
    by_cases hp : (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
    · simp [GW, HS, hp]
    · simp [GW, HS, hp]
  have hSupport : S.indicator GW = GW := by
    funext p
    rw [hST]
    by_cases hp : p.1.1 ≤ T
    · simp [Set.indicator, hp]
    · have ha0 : a p.1 = 0 := haSupport p.1 (lt_of_not_ge hp)
      simp [Set.indicator, hp, GW, ha0]
  exact
    avram_wave6_02_physical_clock_rightcont_stopped_compensated_L1_no_initial_rectangle
      X M hM T S hST MT N hMT μ hμclock hN
      B hBm hBmono hBcover hLocal hFuture
      (ruinTime X x D) (ruinTime_stopping_rightCont_filtration X x D hD)
      GW hGWm hGiN GW hStop hSupport
