-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB131_original_physical_stopped_clipped_gradient_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:08:48.664285+00:00
-- url     : https://prove2.me/submissions/169123a4-14f3-4957-b3ce-c3c933a4e092

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_stopping_time_joint_strict_prestop_region_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB134_clipped_finitecap_gradient_Borel_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    Measurable (fun z : ℝ≥0 × Ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X z.1 z.2 - rightLimit D z.1 z.2
      if z.1 < ρ z.2 then Real.exp (-(q * (z.1 : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1) else 0) := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let F : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
  have hp := postPaymentReserve_cadlag_adapted X x D hD.1.1
  have hsections (t : ℝ≥0) : Measurable (F t) := by
    exact (hp.2.2 t).mono (𝓕.rightCont.le t) le_rfl
  have hright : ∀ ω t, ContinuousWithinAt (fun u : ℝ≥0 => F u ω) (Ici t) t :=
    hp.1
  have hjoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation F hsections hright
  have hc : Measurable (fun z : ℝ≥0 × Ω =>
      if F z.1 z.2 ∈ Icc a b then deriv w (F z.1 z.2) else 1) := by
    have hraw := avram_gbB134_clipped_finitecap_gradient_Borel_measurable
      w C hC hFiniteCap hw_smooth δ hδ j
    change Measurable
      (fun y : ℝ => if y ∈ Icc a b then deriv w y else 1) at hraw
    exact hraw.comp hjoint
  have ht : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have he : Measurable (fun z : ℝ≥0 × Ω => Real.exp (-(q * (z.1 : ℝ)))) :=
    Real.measurable_exp.comp (measurable_const.mul ht).neg
  have hs : MeasurableSet {z : ℝ≥0 × Ω | z.1 < ρ z.2} :=
    avram_gbB133_stopping_time_joint_strict_prestop_region_measurable ρ hρstop
  change Measurable (fun z : ℝ≥0 × Ω =>
    if z.1 < ρ z.2 then Real.exp (-(q * (z.1 : ℝ))) *
      (if F z.1 z.2 ∈ Icc a b then deriv w (F z.1 z.2) else 1)
    else 0)
  exact Measurable.ite hs (he.mul hc) measurable_const
