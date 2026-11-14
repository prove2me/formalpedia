-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb70_original_topcap_compensated_cash_excess_integrable_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:42:15.636202+00:00
-- url     : https://prove2.me/submissions/5f4c34ac-2549-4c54-b29b-b78865e4ab48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb73_original_topcap_full_terminal_strict_cash_uniform_integrable_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_mark_count_majorant
import Theorems.Thm_AvramDividend_Classical_avram_bvb72_original_topcap_predictable_negative_mark_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapTop : C = ⊤) :
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
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    (∀ n, Integrable (J n) P ∧ Integrable (V n) P ∧
      (∫ ω, J n ω ∂P) = (∫ ω, V n ω ∂P)) →
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let E : ℕ → Ω → ℝ := fun n ω =>
      max (F n ω - (w x + (J n ω - V n ω))) 0
    ∃ K : Ω → ℝ, Integrable K P ∧
      (∀ n, ∀ᵐ ω ∂P, ‖E n ω‖ ≤ K ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ U H NX J V hMean δ₂ S F E
  obtain ⟨G, hGI, hGBound⟩ := avram_bvb73_original_topcap_full_terminal_strict_cash_uniform_integrable_envelope X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hFinite hIntensityPositive hCapTop hMean
  obtain ⟨KJ, hKJ0, hNI, hJBound⟩ := avram_bvb_topcap_original_mark_count_majorant X hBV q (le_of_lt hq) w C hC hCapTop hw_cont hw_neg x D hD T hT hFinite
  obtain ⟨KV, hKV0, hVBound⟩ := avram_bvb72_original_topcap_predictable_negative_mark_uniform_bound X hBV q (le_of_lt hq) w C hC hCapTop hw_cont hw_neg x D hD T hT hFinite
  let N : Ω → ℝ := fun ω => ((NX ω) (Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ))).toReal
  let KVConst : ℝ := KV * ((X.ν (Iio (0 : ℝ))).toReal * T)
  let Kenv : Ω → ℝ := fun ω => G ω + |w x| + KJ * N ω + KVConst
  have hKIntegrable : Integrable Kenv P := by
    dsimp [Kenv, KVConst]
    exact ((hGI.add (integrable_const _)).add (hNI.const_mul KJ)).add (integrable_const _)
  refine ⟨Kenv, hKIntegrable, ?_⟩
  intro n
  filter_upwards [hGBound n, hJBound n, hVBound n] with ω hF hJ hV
  have hFle : F n ω ≤ G ω := (le_abs_self (F n ω)).trans (by simpa only [Real.norm_eq_abs] using hF)
  have hJlower : -(KJ * N ω) ≤ J n ω := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hJ)).1
  have hVupper : V n ω ≤ KVConst := (le_abs_self (V n ω)).trans (by simpa only [KVConst, Real.norm_eq_abs] using hV)
  have hGnonneg : 0 ≤ G ω := (norm_nonneg (F n ω)).trans hF
  have hNnonneg : 0 ≤ N ω := ENNReal.toReal_nonneg
  have hConstNonneg : 0 ≤ KVConst := by
    dsimp [KVConst]
    exact mul_nonneg hKV0 (mul_nonneg ENNReal.toReal_nonneg hT.le)
  have hKnonneg : 0 ≤ Kenv ω := by
    dsimp [Kenv]
    exact add_nonneg (add_nonneg (add_nonneg hGnonneg (abs_nonneg (w x))) (mul_nonneg hKJ0 hNnonneg)) hConstNonneg
  have hRewardLe : F n ω - (w x + (J n ω - V n ω)) ≤ Kenv ω := by
    have hwx : -(w x) ≤ |w x| := neg_le_abs (w x)
    dsimp [Kenv]
    linarith
  have hExcessLe : E n ω ≤ Kenv ω := by
    dsimp [E]
    exact max_le hRewardLe hKnonneg
  have hExcessNonneg : 0 ≤ E n ω := by
    dsimp [E]
    exact le_max_right _ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hExcessNonneg] using hExcessLe
