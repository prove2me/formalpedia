-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_source_topcap_compact_generator_physical_fibre_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:57:12.114193+00:00
-- url     : https://prove2.me/submissions/e67fe1dd-880a-4fcf-ac73-336ca1ec22f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_original_predictable_gaussian_gradient_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_le_product_space
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact topcap compact HJB drift is integrable on physical time fibres. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ a b B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (ha : 0 < a) (hau : a < u + δ) (hvb : v < b) (hb : b < B)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    Integrable (fun ω : Ω =>
      ∫ t : ℝ≥0, R (t, ω) ∂
        (((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let R : ℝ≥0 × Ω → ℝ := fun p =>
    ρ p * (if Y p ∈ Icc (u + δ) v then
      X.generator w (Y p) - q * w (Y p) else 0)
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨μ, _, hμclock, hR, _, _, _⟩ :=
    avram_ubv_loc6_topcap_original_predictable_gaussian_gradient_HJB_source
      X x D C hD hTop w hw_smooth hw_cont hw_neg q hw_gen hw_grad
      u v δ a b B hu hδ hδone huv hv ha hau hvb hb T
  let θ : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  haveI hFiniteTime : IsFiniteMeasure
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) := by
    infer_instance
  haveI hFiniteθ : IsFiniteMeasure θ :=
    Measure.isFiniteMeasure_map
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) Real.toNNReal
  let ν : Measure (ℝ≥0 × Ω) := θ.prod P
  have hPred : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) :=
    avram_p3_b_bvjump_original_predictable_le_product_space 𝓕
  have hμtrim : μ = ν.trim hPred := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    ext A hA
    rw [trim_measurableSet_eq hPred hA]
    exact hμclock A hA
  have hTrimI : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; Integrable R (ν.trim hPred)) := by
    simpa only [← hμtrim] using hR
  have hProdI : Integrable R ν :=
    integrable_of_integrable_trim hPred hTrimI
  have hRight : Integrable (fun ω =>
      ∫ t : ℝ≥0, R (t, ω) ∂θ) P :=
    hProdI.integral_prod_right
  change Integrable (fun ω : Ω => ∫ t : ℝ≥0, R (t, ω) ∂θ) P
  exact hRight
