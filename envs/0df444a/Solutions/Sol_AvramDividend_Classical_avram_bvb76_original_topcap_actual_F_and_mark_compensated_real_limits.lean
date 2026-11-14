-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb76_original_topcap_actual_F_and_mark_compensated_real_limits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:42:58.177639+00:00
-- url     : https://prove2.me/submissions/51395908-998d-4c7a-995e-cc93feb8723a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb73_original_topcap_full_terminal_strict_cash_uniform_integrable_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bvb79_original_topcap_VminusJ_real_limit_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory Filter AvramDividend.Classical
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
    ∀ᵐ ω ∂P, ∃ f k : ℝ,
      Tendsto (fun n : ℕ => F n ω) atTop (𝓝 f) ∧
      Tendsto (fun n : ℕ => V n ω - J n ω) atTop (𝓝 k) := by
  classical
  intro δ U H NX J V hComp δ' S F E
  have hBound :=
    avram_bvb73_original_topcap_full_terminal_strict_cash_uniform_integrable_envelope
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hFinite
      hIntensityPositive hCapTop hComp
  change ∃ G : Ω → ℝ, Integrable G P ∧
    (∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ G ω) at hBound
  rcases hBound with ⟨G, hGI, hB⟩
  have hBAll : ∀ᵐ ω ∂P, ∀ n, ‖F n ω‖ ≤ G ω :=
    MeasureTheory.ae_all_iff.mpr hB
  have hMono :=
    avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
      X x C D hD w q T hT
  change ∀ᵐ ω ∂P,
    ∀ n k : ℕ, n ≤ k → F n ω ≤ F k ω at hMono
  have hMark :=
    avram_bvb79_original_topcap_VminusJ_real_limit_ae
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hFinite
      hIntensityPositive hCapTop hComp
  change ∀ᵐ ω ∂P, ∃ k : ℝ,
    Tendsto (fun n : ℕ => V n ω - J n ω) atTop (𝓝 k) at hMark
  filter_upwards [hBAll, hMono, hMark] with ω hωB hωM hωK
  have hMonotone : Monotone (fun n : ℕ => F n ω) :=
    fun n k hn => hωM n k hn
  have hBdd : BddAbove (Set.range (fun n : ℕ => F n ω)) := by
    refine ⟨G ω, ?_⟩
    rintro z ⟨n, rfl⟩
    exact (show F n ω ≤ ‖F n ω‖ by
      simpa only [Real.norm_eq_abs] using le_abs_self (F n ω)).trans (hωB n)
  obtain ⟨f, hf⟩ := Real.tendsto_of_bddAbove_monotone hBdd hMonotone
  obtain ⟨k, hk⟩ := hωK
  exact ⟨f, k, hf, hk⟩
