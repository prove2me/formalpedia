-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_randomstop_discounted_C2_negative_jump_pathwise_quadratic_energy_from_true_source_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:54:03.363214+00:00
-- url     : https://prove2.me/submissions/f6ec3d23-5a3a-46bf-a335-d6061b372119

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_source_jump_complete_generator_compensation_with_quadratic_negative_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_real_quadratic_lintegral_energy_implies_integrable_product
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_intrinsic_negative_jump_occupation_equals_physical_levy_product_of_future_rectangles
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_discounted_ruinstopped_C2_source_jump_fibre_quadratic_energy_ae_from_global_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Almost-sure quadratic jump-count energy of the original stopped-discounted negative C² Taylor kernel under true source-clock transport. -/
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
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q),
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
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
    ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ =>
        GW ((p.1, ω), p.2) * GW ((p.1, ω), p.2)) (NX ω) := by
  classical
  intro NX K M hM T S hST MT N hMT μ hμ hμclock hN
    B hBm hBmono hBcover hLocal hFuture τ hτ q hq a Y J HS GW
  have hWeight :=
    avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
      (𝓕 := 𝓕) τ hτ q hq T
  obtain ⟨hHSm, _, _⟩ :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have haLift : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1) :=
    hWeight.1.comp measurable_fst
  have hGWm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] GW := haLift.mul hHSm
  have hFull :=
    avram_wave6_04_actual_randomstop_source_jump_complete_generator_compensation_with_quadratic_negative_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      M hM T S hST MT N hMT μ hμ hμclock hN
      B hBm hBmono hBcover hLocal hFuture τ hτ q hq
      (fun _ : ℕ => (∅ : Set ℝ))
      (by intro n; exact MeasurableSet.empty)
      (by intro n; exact Set.empty_subset _)
      (by intro i j _; rfl)
      (by apply Set.Subset.antisymm
          · intro z hz; exact (Set.mem_iInter.mp hz 0)
          · exact Set.empty_subset _)
  have hSqProd := hFull.2.2.2.1
  have hGWmulIntN : Integrable (fun p => GW p * GW p) N := by
    rw [hN]
    exact avram_wave6_04_real_quadratic_lintegral_energy_implies_integrable_product
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) GW hGWm hSqProd
  have hMTN : MT = N :=
    avram_wave6_04_true_source_intrinsic_negative_jump_occupation_equals_physical_levy_product_of_future_rectangles
      X M hM T S hST MT N hMT μ hμ hμclock hN
      B hBm hBmono hBcover hLocal hFuture
  have hSm : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S := by
    rw [hST]
    exact avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable 𝓕 T
  have hSupp : S.indicator (fun p => GW p * GW p) =
      (fun p => GW p * GW p) := by
    funext p
    rw [hST]
    by_cases hp : p.1.1 ≤ T
    · simp [Set.indicator, hp]
    · have ha0 : a p.1 = 0 := hWeight.2.2 p.1 (lt_of_not_ge hp)
      simp [Set.indicator, hp, GW, ha0]
  have hGWmulIntM : Integrable (fun p => GW p * GW p) M := by
    have hRestr : Integrable (fun p => GW p * GW p) (M.restrict S) := by
      rw [← hMT, hMTN]
      exact hGWmulIntN
    have hInd := (integrable_indicator_iff hSm).2 hRestr
    simpa only [hSupp] using hInd
  exact
    avram_wave6_04_actual_discounted_ruinstopped_C2_source_jump_fibre_quadratic_energy_ae_from_global_L2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      τ hτ q hq T M hM hGWm hGWmulIntM