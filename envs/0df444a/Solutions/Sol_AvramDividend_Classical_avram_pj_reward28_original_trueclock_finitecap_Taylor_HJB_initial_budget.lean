-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward28_original_trueclock_finitecap_Taylor_HJB_initial_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:42:17.715916+00:00
-- url     : https://prove2.me/submissions/d47c1c1a-7a56-4bd0-8f81-35c7d5d27ff3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward27_original_stopped_Taylor_with_nonpositive_drift_initial_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_discounted_true_stopped_generator_L1_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (Ccap : ℝ≥0∞) (hCcap : 0 < Ccap) (hFinite : Ccap ≠ ⊤)
    (hAd : IsAdmissibleLe X x Ccap D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cap : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Ccap})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) (hvCap : v < Ccap.toReal)
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < Ccap →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < Ccap → 1 ≤ deriv w y)
    (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
          (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
    let B : (Ω → ℝ≥0) → Ω → ℝ := fun σ ω =>
      ∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0 ∂μT
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont
        (fun ω => (σ ω : WithTop ℝ≥0))),
      Integrable (fun ω => J σ ω + B σ ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => J σ ω + B σ ω) ω ≤ 0) := by
  intro a Y H HS GW NX μT J R B σ hσ
  obtain ⟨hBI, hBnonpos⟩ :=
    avram_ubv_finite9_discounted_true_stopped_generator_L1_nonpos
      X x D Ccap hAd hCcap hFinite
      w hw_cap hw_cont hw_neg q hq hw_gen hw_grad
      u v δ hu hδ hδone huv hvCap T σ hσ
  have hBae : ∀ᵐ ω ∂P, B σ ω ≤ 0 :=
    Filter.Eventually.of_forall hBnonpos
  exact avram_pj_reward27_original_stopped_Taylor_with_nonpositive_drift_initial_budget
    X x D hD w C u v δ hw hw_cont hw_neg
    hu hδ hδone huv hv q hq T σ hσ (B σ) hBI hBae