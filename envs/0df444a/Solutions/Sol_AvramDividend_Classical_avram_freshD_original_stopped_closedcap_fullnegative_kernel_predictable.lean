-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_stopped_closedcap_fullnegative_kernel_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:58:26.926267+00:00
-- url     : https://prove2.me/submissions/d98aab54-068a-414f-926c-72f044176fbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_prestate_closedcap_negative_mark_predictable_mask
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_stopped_discount_fullnegative_value_product_predictable
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_bounded_stop_fullnegative_kernel_mask_factorisation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H := by
  classical
  intro Y NX μT H
  have hcore : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (fun p : (ℝ≥0 × Ω) × ℝ =>
        (((if p.1.1 ≤ (n : ℝ≥0)
            then Real.exp (-(q * (p.1.1 : ℝ))) else 0) *
          (if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞)
            then (1 : ℝ) else 0)) *
          ((if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
            then (1 : ℝ) else 0) *
            (w (Y p.1 + p.2) - w (Y p.1))))) := by
    simpa only [Y] using
      avram_freshD_original_true_stopped_discount_fullnegative_value_product_predictable
        X x q hq w hw_cont hw_neg D hD n σ hσstop
  have hmask : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ |
        0 < p.1.1 ∧ 0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0} := by
    simpa only [Y] using
      avram_freshD_original_true_prestate_closedcap_negative_mark_predictable_mask
        X x D hD C
  have hEq : H = fun p =>
      (((if p.1.1 ≤ (n : ℝ≥0) then Real.exp (-(q * (p.1.1 : ℝ))) else 0) *
          (if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞) then (1 : ℝ) else 0)) *
        ((if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
          (w (Y p.1 + p.2) - w (Y p.1)))) *
        (if 0 < p.1.1 ∧ 0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0
         then (1 : ℝ) else 0) := by
    funext p
    simpa only [Y, NX, μT, H] using
      (avram_freshD_original_true_bounded_stop_fullnegative_kernel_mask_factorisation
        X x q C w D n σ hσbound p)
  rw [hEq]
  exact hcore.mul (measurable_const.ite hmask measurable_const)
