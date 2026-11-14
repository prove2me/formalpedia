-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb34_original_zero_survivor_full_Ioc_cash_terminal_le_HJB_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:11:38.842131+00:00
-- url     : https://prove2.me/submissions/b5a7fa33-4bbc-4a38-8ff5-90b9d7c6475c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
import Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
import Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_zero_reserve_linear_source_forces_nonnegative_drift
import Theorems.Thm_AvramDividend_Classical_avram_bvb36_source_physical_discount_Ioc_lintegral_eq_ofReal_real_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_everywhere_zero_reserve_forces_exact_initial_capital_zero
import Theorems.Thm_AvramDividend_Classical_avram_bvb38_original_discounted_cashrate_ENNReal_to_real_terminal_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0) (hgrid : ∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1), if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1)))))
    (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0)
    (hPre : ∀ᵐ ω ∂P, ∀ n i, Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n (i + 1)) = riskProcess X x D (u n (i + 1)) ω)
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧ (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧ 0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) * (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map (fun t : ℝ≥0 => (t, X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let G : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0)
    let K : ℕ → Ω → ℝ := fun n ω => (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) →
      (NX ω) (Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)) = 0 →
      ((S : ℝ≥0∞) < ruinTime X x D ω) →
      (∀ t : ℝ≥0, t ≤ S → riskProcess X x D t ω = 0) →
      ((∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + Real.exp (-(q * T)) * w 0) ≤ w x + (w 0 * (X.ν (Iio (0 : ℝ))).toReal) * (∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ))  := by
  intro δ S F U H NX G K
  by_cases hd : 0 ≤ X.drift
  · have hA := avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate X hX hBV hActivity hd q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x D hD S (by exact_mod_cast hT)
    filter_upwards [hA] with ω hω
    intro hSource hNeg hSurv hZero
    have hNoJump : ∀ t : ℝ≥0, t ∈ Ioc (0 : ℝ≥0) S → X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = 0 := by
      intro t ht; exact avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim X ω S hSource t ht.2
    let m : ℝ := (X.ν (Iio (0 : ℝ))).toReal
    let c : ℝ := ∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ)
    let e : ℝ := Real.exp (-(q * T))
    let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
    let full : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) T, f t ∂(dividendMeasure D ω)
    have hm : 0 ≤ m := ENNReal.toReal_nonneg
    have hc : 0 ≤ c := integral_nonneg (fun t => (Real.exp_pos _).le)
    have hClock := avram_bvb36_source_physical_discount_Ioc_lintegral_eq_ofReal_real_integral q T
    have hBound : full ≤ ENNReal.ofReal ((q + m) * w 0) * ENNReal.ofReal c := by
      have hRaw := hω hSurv hZero hNoJump
      have hSEq : (S : ℝ) = T := rfl
      rw [hSEq, hClock] at hRaw
      simpa only [full, f, m, c] using hRaw
    have hDiscount : q * c + e = 1 := by
      have hb := avram_bvb23_original_discounted_zero_contact_budget_identity q T hq hT.le
      rw [intervalIntegral.integral_of_le hT.le] at hb
      simpa only [c, e, neg_mul] using hb
    have hCash := avram_bvb38_original_discounted_cashrate_ENNReal_to_real_terminal_budget
      full q m (w 0) c e hq.le hm hw0 hc hDiscount hBound
    have hX0 : x = 0 := avram_bvb24_original_everywhere_zero_reserve_forces_exact_initial_capital_zero X x C D hD ω S hZero
    change full.toReal + e * w 0 ≤ w x + (w 0 * m) * c
    rw [hX0]
    nlinarith [hCash]
  · apply Filter.Eventually.of_forall
    intro ω hSource hNeg hSurv hZero
    have hNonneg := avram_bvb32_original_zero_reserve_linear_source_forces_nonnegative_drift X x C D hD ω S (by exact_mod_cast hT) hZero hSource
    exact False.elim (hd hNonneg)
