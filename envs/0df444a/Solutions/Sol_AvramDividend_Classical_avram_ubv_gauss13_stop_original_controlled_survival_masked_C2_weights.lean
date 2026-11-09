-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_original_controlled_survival_masked_C2_weights
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:00:37.567102+00:00
-- url     : https://prove2.me/submissions/bf29a291-1a69-4673-94f5-d3d69478196c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_sampled_survival_predictable_coefficients
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original controlled Gaussian C2 coefficients retain left-grid predictability through true sampled survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ))) :
    let G : ℝ≥0 → Ω → ℝ :=
      fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0
    let H : ℝ≥0 → Ω → ℝ :=
      fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0
    ∀ i,
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then G (e i) ω else 0) ∧
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then H (e i) ω else 0) := by
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0
  let H : ℝ≥0 → Ω → ℝ := fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0
  change ∀ i,
    Measurable[𝓕.rightCont (e i)]
      (fun ω => if i < K ω then G (e i) ω else 0) ∧
    Measurable[𝓕.rightCont (e i)]
      (fun ω => if i < K ω then H (e i) ω else 0)
  have hGP : IsStronglyPredictable 𝓕.rightCont G := by
    exact avram_wave3_04_source_stopped_discounted_deriv_predictable
      X x D hD w q T
  have hHP : IsStronglyPredictable 𝓕.rightCont H := by
    exact avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
      X x D hD w C hw q T
  have hGM : ∀ i, Measurable[𝓕.rightCont (e i)] (G (e i)) := by
    intro i
    exact (hGP.stronglyAdapted (e i)).measurable
  have hHM : ∀ i, Measurable[𝓕.rightCont (e i)] (H (e i)) := by
    intro i
    exact (hHP.stronglyAdapted (e i)).measurable
  exact avram_ubv_gauss13_stop_sampled_survival_predictable_coefficients
    e he 𝓖 h𝓖 K hK (fun i => G (e i)) (fun i => H (e i)) hGM hHM
