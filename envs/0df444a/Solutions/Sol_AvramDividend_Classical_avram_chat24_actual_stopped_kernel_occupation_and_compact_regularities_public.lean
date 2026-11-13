-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_actual_stopped_kernel_occupation_and_compact_regularities_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:53:27.023636+00:00
-- url     : https://prove2.me/submissions/10f1e6c3-ec0c-4ca0-9839-fffe67c71e71

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time
import Theorems.Thm_AvramDividend_Classical_avram_bv_small13_original_rightcont_predictable_finite_clock_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_chat24_actual_stopped_predictable_kernel_occupation_L1_public

import Theorems.Thm_AvramDividend_Classical_avram_chat24_C1_positive_band_analytic_certificate

import Theorems.Thm_AvramDividend_Classical_avram_chat24_BV_C1_discounted_compact_kernel_intensity_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 ≤ x) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let Ξ : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ)) :=
      fun ω => @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) inferInstance
        (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ))
        (fun p => ((p.1, ω), p.2)) (NX ω)
    a ≤ b ∧ Measurable[𝓕.rightCont.predictable] Y ∧
    ContinuousOn (fun y => X.drift * deriv w y - q * w y) (Icc a b) ∧
    Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] H ∧ Integrable H (P.bind Ξ) := by
  classical
  intro S a b τ Y NX H μ Ξ
  letI : IsProbabilityMeasure P := X.isProbability
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ := by dsimp [a]; have := min_le_left δ 1; linarith
  have ha2 : a ≤ 2 := by dsimp [a]; have := min_le_right δ 1; linarith
  have hab : a ≤ b := by dsimp [b]; nlinarith [mul_nonneg hT hd.le]
  have hs : ContDiffOn ℝ 1 w (Ioi 0) := hw_smooth.mono (by
    intro y hy
    exact ⟨hy, by simp only [hTop, ENNReal.ofReal_lt_top]⟩)
  have hcont := (avram_chat24_C1_positive_band_analytic_certificate
    w hw_cont hw_neg hs a b X.drift q ha hab).2.1
  obtain ⟨ρ, hρ, hρclock⟩ :=
    avram_bv_small13_original_rightcont_predictable_finite_clock_exists X x D hD.1.1 S
  have hτcoe (ω : Ω) : (τ ω : ℝ≥0∞) = min (ruinTime X x D ω) (S : ℝ≥0∞) :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
  have hτBound (ω : Ω) : τ ω ≤ S := by
    have hb : (τ ω : ℝ≥0∞) ≤ (S : ℝ≥0∞) := (hτcoe ω).trans_le (min_le_right _ _)
    exact_mod_cast hb
  have hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : ℝ≥0∞)) := by
    intro i
    change MeasurableSet[𝓕.rightCont i] {ω | (τ ω : ℝ≥0∞) ≤ (i : ℝ≥0∞)}
    by_cases hSi : S ≤ i
    · convert MeasurableSet.univ using 1
      ext ω
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact ENNReal.coe_le_coe.mpr ((hτBound ω).trans hSi)
    · have hSi' : ¬ (S : ℝ≥0∞) ≤ (i : ℝ≥0∞) := fun h => hSi (ENNReal.coe_le_coe.mp h)
      have heq : {ω | (τ ω : ℝ≥0∞) ≤ (i : ℝ≥0∞)} =
          {ω | ruinTime X x D ω ≤ (i : ℝ≥0∞)} := by
        ext ω
        change (τ ω : ℝ≥0∞) ≤ (i : ℝ≥0∞) ↔ ruinTime X x D ω ≤ (i : ℝ≥0∞)
        rw [hτcoe ω]
        simp only [min_le_iff, hSi', or_false]
      rw [heq]
      exact avram_wave4_03_actual_ruinTime_rightCont_stopping_time X x D hD.1.1 i
  let A : ℝ≥0 × Ω → ℝ := fun p => if p.1 ≤ S then Real.exp (-(q * (p.1 : ℝ))) else 0
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => A p.1 *
    (if Y p.1 ∈ Icc a b ∧ p.2 < 0 then w (Y p.1 + p.2) - w (Y p.1) else 0)
  obtain ⟨hY, hG, hGi⟩ := avram_chat24_BV_C1_discounted_compact_kernel_intensity_L1
    X hBV (x + δ) D hD.1.1 w hw_cont hw_neg hs q hq.le a b ha ha2 hab S ρ hρ
  have hHG : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0 := by
    funext p
    by_cases ht : p.1.1 ≤ τ p.1.2
    · have he : (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) := ENNReal.coe_le_coe.mpr ht
      have htS : p.1.1 ≤ S := ht.trans (hτBound p.1.2)
      simp only [H, G, A, he, htS, if_true, true_and, mul_ite, mul_zero]
    · have he : ¬ (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) := fun h => ht (ENNReal.coe_le_coe.mp h)
      simp only [H, he, false_and, if_false]
  have hocc := avram_chat24_actual_stopped_predictable_kernel_occupation_L1_public
    X S ρ hρ hρclock G hG hGi τ hτBound hτ H hHG
  exact ⟨hab, hY, hcont, hocc⟩
