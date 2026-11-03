-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_discounted_ruin_stopped_Taylor_pathwise_compensator_L1_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:34:35.766229+00:00
-- url     : https://prove2.me/submissions/ecb39ea9-c4f2-4f17-9c8a-0a2f5622d0d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_controlled_stopped_Taylor_jump_L1_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
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
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
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
    ∀ (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hνBand : ∀ k, (X.ν.restrict (Iio (0 : ℝ))) (B k) < ⊤)
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (q : ℝ) (hq : 0 ≤ q),
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
    let η : Measure ℝ≥0 := (((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal)
    let Comp : Ω → ℝ := fun ω =>
      ∫ t, ∫ z, GW ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂η
    let Jump : Ω → ℝ := fun ω =>
      ∫ p, GW ((p.1, ω), p.2) ∂(NX ω)
    Integrable (fun ω => Jump ω - Comp ω) P ∧
    (∫ ω, (Jump ω - Comp ω) ∂P) = 0)  := by
  classical
  obtain ⟨μ, hμ, hμclock, hSigned⟩ :=
    avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini X T
  refine ⟨μ, hμ, hμclock, ?_⟩
  intro NX K M hM S hST MT N hMT hN
    B hBm hBmono hBcover hνBand hFuture
    q hq a Y J HS GW η Comp Jump
  have hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞ := by
    intro k
    exact
      avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
        X K (by intro ω; rfl) M hM T S MT N hMT μ hμ hμclock hN
        (B k) (hBm k) (hνBand k) hFuture
  have hCentered :=
    avram_wave6_02_actual_discounted_controlled_stopped_Taylor_jump_L1_mean_zero
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      M hM T S hST MT N hMT μ hμ hμclock hN
      B hBm hBmono hBcover hLocal hFuture q hq
  obtain ⟨ha, haBound, haSupport⟩ :=
    avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
      (𝓕 := 𝓕) q hq T
  obtain ⟨hHSm, _, _⟩ :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  have hGWi :=
    (avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ a ha 1 haBound).1
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have haLift : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1) :=
    ha.comp measurable_fst
  have hGWm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] GW :=
    haLift.mul hHSm
  have hGiN : Integrable GW
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := hGWi
  obtain ⟨hCompInt, hCompMeanProd⟩ := hSigned GW hGWm hGiN
  have hCompMean : (∫ ω, Comp ω ∂P) = (∫ p, GW p ∂N) := by
    rw [hN]
    exact hCompMeanProd
  have hConst : Integrable (fun _ : Ω => ∫ p, GW p ∂N) P := integrable_const _
  have hJumpInt : Integrable Jump P := by
    refine (hCentered.1.add hConst).congr ?_
    filter_upwards with ω
    dsimp [Jump]
    ring
  have hJumpMean : (∫ ω, Jump ω ∂P) = (∫ p, GW p ∂N) := by
    have hsub : (∫ ω, (Jump ω - ∫ p, GW p ∂N) ∂P) =
        (∫ ω, Jump ω ∂P) - (∫ p, GW p ∂N) := by
      rw [integral_sub hJumpInt hConst]
      simp
    apply sub_eq_zero.mp
    calc
      (∫ ω, Jump ω ∂P) - (∫ p, GW p ∂N) =
          (∫ ω, (Jump ω - ∫ p, GW p ∂N) ∂P) := hsub.symm
      _ = 0 := hCentered.2
  exact ⟨hJumpInt.sub hCompInt, by
    rw [integral_sub hJumpInt hCompInt, hJumpMean, hCompMean]
    simp⟩
