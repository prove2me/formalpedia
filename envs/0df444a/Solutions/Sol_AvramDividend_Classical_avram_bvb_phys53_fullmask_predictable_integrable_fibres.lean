-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys53_fullmask_predictable_integrable_fibres
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:09:56.487653+00:00
-- url     : https://prove2.me/submissions/1de2fb07-32da-49b1-86d1-b23979f3f8ad

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys55_fullmask_reward_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys56_fullmask_reward_aefibre_integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original full-mask reward's predictable and fibre-integrable components. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
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
    (∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (H n)) ∧
    (∀ n, ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H n ((p.1, ω), p.2)) (NX ω)) := by
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
  change (∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (H n)) ∧
    (∀ n, ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H n ((p.1, ω), p.2)) (NX ω))
  constructor
  · exact avram_bvb_phys55_fullmask_reward_marked_predictable
      X hBV q hq w C hC hFinite hw_cont hw_neg x D hD T hT hActivity
  · exact avram_bvb_phys56_fullmask_reward_aefibre_integrable
      X hBV q hq w C hC hFinite hw_cont hw_neg x D hD T hT hActivity
