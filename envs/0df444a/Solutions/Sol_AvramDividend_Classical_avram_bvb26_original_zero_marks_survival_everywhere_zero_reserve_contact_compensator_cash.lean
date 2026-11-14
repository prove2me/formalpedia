-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb26_original_zero_marks_survival_everywhere_zero_reserve_contact_compensator_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:22:44.159339+00:00
-- url     : https://prove2.me/submissions/6f58363f-2a82-4baa-9a63-897c5a06d7d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_zero_contact_survivor_uniform_full_cash_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_zero_contact_survivor_exact_K_limit_and_G_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bvb29_source_uniform_discounted_cash_upper_bound_positive_part_limit
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
      (∀ t : ℝ≥0, t ≤ S →
        riskProcess X x D t ω = 0) →
      Tendsto (fun n => if ruinTime X x D ω = 0 then 0 else
        max (F n ω - (w x + ((-K n ω) + G n ω))) 0)
        atTop (𝓝 0) := by
  intro δ S F U H NX G K
  have hCash := avram_bvb30_original_zero_contact_survivor_uniform_full_cash_ceiling
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
    T hT u hgrid hmono huniform B hB hAllB hPre hFinite hActivity
  have hKG := avram_bvb30_original_zero_contact_survivor_exact_K_limit_and_G_vanish
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
    T hT u hgrid hmono huniform B hB hAllB hPre hFinite hActivity
  filter_upwards [hCash, hKG] with ω hc hk
  intro hs hn hr hz
  by_cases hR : ruinTime X x D ω = 0
  · simpa only [hR, ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hf := hc hs hn hr hz
    have hkg := hk hs hn hr hz
    have hBound : w x + (w 0 * (X.ν (Iio (0 : ℝ))).toReal) * (∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ)) ≤
        w x - (-(w 0 * (X.ν (Iio (0 : ℝ))).toReal) * (∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ))) := by nlinarith
    have hLimit :=
      avram_bvb29_source_uniform_discounted_cash_upper_bound_positive_part_limit
        (fun n => F n ω) (fun n => K n ω) (fun n => G n ω)
        (w x) (w x + (w 0 * (X.ν (Iio (0 : ℝ))).toReal) * (∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ)))
        (-(w 0 * (X.ν (Iio (0 : ℝ))).toReal) * (∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ)))
        hf hkg.1 hkg.2 hBound
    simpa only [hR, ite_false] using hLimit
