-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_rate_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:37:39.347209+00:00
-- url     : https://prove2.me/submissions/fed749b1-6cf9-4a3a-89cd-64060982adf1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
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
    ∀ n, Integrable (V n) P := by
  intro δ U H NX J V n
  let Tnn : ℝ≥0 := ⟨T, hT.le⟩
  obtain ⟨μ, hμfinite, hμclock, hFubini⟩ :=
    avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
      X Tnn
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hνfinite : ν Set.univ < ⊤ := by
    simpa only [ν, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter] using hActivity
  haveI : IsFiniteMeasure μ := ⟨hμfinite⟩
  haveI : IsFiniteMeasure ν := ⟨hνfinite⟩
  have hPred :=
    AvramDividend.Classical.avram_bvb_topcap_original_marked_predictable
      X hBV q hq w C hC hCapTop hw_cont hw_neg x D hD T hT hActivity
  have hMeas : Measurable (H n) := by
    simpa only [δ, U, H] using hPred n
  obtain ⟨K, hK, hBound⟩ :=
    AvramDividend.Classical.avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
      X hBV q hq w C hC hCapTop hw_cont hw_neg x D hD T hT hActivity μ hμfinite hμclock
  have hDom : ∀ᵐ p ∂(μ.prod ν), ‖H n p‖ ≤ K := by
    filter_upwards [hBound n] with p hp
    simpa only [Real.norm_eq_abs, ν] using hp
  have hKernel : Integrable (H n) (μ.prod ν) := by
    exact (integrable_const K).mono' hMeas.aestronglyMeasurable hDom
  have hConclusion := hFubini (H n) hMeas hKernel
  exact hConclusion.1
