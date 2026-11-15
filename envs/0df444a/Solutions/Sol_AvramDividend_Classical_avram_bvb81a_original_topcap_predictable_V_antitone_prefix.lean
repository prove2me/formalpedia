-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb81a_original_topcap_predictable_V_antitone_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:27:41.656773+00:00
-- url     : https://prove2.me/submissions/550d6e79-c68d-4229-b5df-ad1754589440

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_pathwise_all_marks_uniform_kernel_bound
import Theorems.Thm_AvramDividend_Classical_avram_chat24_predictable_section_measurable_public
import Theorems.Thm_AvramDividend_Classical_avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass
import Theorems.Thm_AvramDividend_Classical_avram_bvb81b_original_topcap_negative_mark_kernel_antitone_prefix
import Theorems.Thm_AvramDividend_Classical_avram_bvb81c_finite_product_bounded_measurable_antitone_integrals
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
    ∀ᵐ ω ∂P, Antitone (fun n : ℕ => V n ω) := by
  classical
  intro δ U H NX J V
  have hPred :=
    avram_bvb_topcap_original_marked_predictable
      X hBV q hq.le w C hC hCapTop hw_cont hw_neg x D hD T hT hFinite
  have hAnti :=
    avram_bvb81b_original_topcap_negative_mark_kernel_antitone_prefix
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      hFinite hIntensityPositive hCapTop
  obtain ⟨K, hK, hBound⟩ :=
    avram_bvb_topcap_original_pathwise_all_marks_uniform_kernel_bound
      X hBV q hq.le w C hC hCapTop hw_cont hw_neg x D hD T hT hFinite
  change ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0, ∀ z : ℝ,
    |H n ((t, ω), z)| ≤ K at hBound
  filter_upwards [hBound] with ω hωBound
  let μTime : Measure ℝ≥0 :=
    (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
  let νNeg : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hν : νNeg Set.univ < ⊤ := by simpa [νNeg] using hFinite
  have hμ : μTime Set.univ < ⊤ := by
    simpa only [μTime] using
      avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass T hT
  letI : IsFiniteMeasure νNeg := ⟨hν⟩
  letI : IsFiniteMeasure μTime := ⟨hμ⟩
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hSection : Measurable (fun t : ℝ≥0 => (t, ω)) :=
    avram_chat24_predictable_section_measurable_public 𝓕.rightCont ω
  have hJoint (k : ℕ) :
      Measurable (fun p : ℝ≥0 × ℝ => H k ((p.1, ω), p.2)) := by
    have hp : Measurable (H k) := hPred k
    exact hp.comp ((hSection.comp measurable_fst).prodMk measurable_snd)
  have hUniform : ∀ n : ℕ, ∀ t : ℝ≥0, ∀ z : ℝ,
      ‖H n ((t, ω), z)‖ ≤ K := by
    intro n t z
    simpa only [Real.norm_eq_abs] using hωBound n t z
  have hResult :=
    avram_bvb81c_finite_product_bounded_measurable_antitone_integrals
      μTime νNeg (fun n t z => H n ((t, ω), z)) K hK
      (fun n => hJoint n) hUniform
      (fun n m hnm t z => hAnti n m hnm t ω z)
  simpa only [V, μTime, νNeg] using hResult
