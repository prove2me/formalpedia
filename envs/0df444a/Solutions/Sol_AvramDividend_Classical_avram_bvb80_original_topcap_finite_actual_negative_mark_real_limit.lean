-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb80_original_topcap_finite_actual_negative_mark_real_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:44:45.866075+00:00
-- url     : https://prove2.me/submissions/385f853a-73f9-4225-adec-f9c5eeebaa9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb80f_original_marked_J_finite_count_uniform_kernel
import Theorems.Thm_AvramDividend_Classical_avram_bvb80e_original_marked_J_restrict_fullnegative_finite_T
import Theorems.Thm_AvramDividend_Classical_avram_bvb80c_finite_measure_bounded_antitone_integral_converges
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb81b_original_topcap_negative_mark_kernel_antitone_prefix
import Theorems.Thm_AvramDividend_Classical_avram_chat24_predictable_section_measurable_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set MeasureTheory Filter AvramDividend.Classical
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
    ∀ᵐ ω ∂P, ∃ j : ℝ,
      Tendsto (fun n : ℕ => J n ω) atTop (𝓝 j)  := by
  classical
  intro δ U H NX J V hComp δ' S F E
  let A : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)
  have hCount :=
    avram_bvb80f_original_marked_J_finite_count_uniform_kernel
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      hFinite hIntensityPositive hCapTop
  have hRestrict :=
    avram_bvb80e_original_marked_J_restrict_fullnegative_finite_T
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      hFinite hIntensityPositive hCapTop
  have hPred :=
    avram_bvb_topcap_original_marked_predictable
      X hBV q hq.le w C hC hCapTop hw_cont hw_neg x D hD T hT hFinite
  have hAnti :=
    avram_bvb81b_original_topcap_negative_mark_kernel_antitone_prefix
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      hFinite hIntensityPositive hCapTop
  filter_upwards [hCount] with ω hω
  rcases hω with ⟨hμ, K, hK, hBound⟩
  let μ : Measure (ℝ≥0 × ℝ) := (NX ω).restrict A
  have hμfinite : μ Set.univ < ⊤ := by simpa [μ, A] using hμ
  letI : IsFiniteMeasure μ := ⟨hμfinite⟩
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hMeas : ∀ n : ℕ, Measurable
      (fun p : ℝ≥0 × ℝ => H n ((p.1, ω), p.2)) := by
    intro n
    exact (hPred n).comp
      (((avram_chat24_predictable_section_measurable_public
          𝓕.rightCont ω).comp measurable_fst).prodMk measurable_snd)
  obtain ⟨j, hj⟩ :=
    avram_bvb80c_finite_measure_bounded_antitone_integral_converges
      μ (fun n p => H n ((p.1, ω), p.2)) K hK hMeas hBound
      (fun n m hnm p => hAnti n m hnm p.1 ω p.2)
  refine ⟨j, ?_⟩
  have heq : ∀ n : ℕ,
      J n ω = ∫ p, H n ((p.1, ω), p.2) ∂μ :=
    fun n => by simpa only [J, μ, A] using hRestrict ω n
  simpa only [heq] using hj
