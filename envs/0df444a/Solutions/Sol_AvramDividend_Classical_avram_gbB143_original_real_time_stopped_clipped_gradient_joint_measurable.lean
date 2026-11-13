-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:31:51.393864+00:00
-- url     : https://prove2.me/submissions/30500276-c240-41e1-972e-40ea7469dfe3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_physical_stopped_clipped_gradient_joint_measurable
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
    Measurable (fun z : ℝ × Ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X (Real.toNNReal z.1) z.2 - rightLimit D (Real.toNNReal z.1) z.2
      if Real.toNNReal z.1 < ρ z.2 then Real.exp (-(q * z.1)) *
        (if Y ∈ Icc a b then deriv w Y else 1) else 0) := by
  have hb := avram_gbB131_original_physical_stopped_clipped_gradient_joint_measurable
    X q hq w C hC hFiniteCap hw_smooth x D hD ρ hρstop δ hδ j
  have ht : Measurable (fun z : ℝ × Ω => Real.toNNReal z.1) :=
    measurable_real_toNNReal.comp measurable_fst
  have hm : Measurable (fun z : ℝ × Ω => (Real.toNNReal z.1, z.2)) :=
    ht.prodMk measurable_snd
  have hbase := hb.comp hm
  have hfactor : Measurable
      (fun z : ℝ × Ω => Real.exp
        (-(q * (z.1 - (Real.toNNReal z.1 : ℝ))))) := by
    fun_prop
  have hmul := hfactor.mul hbase
  convert hmul using 1
  funext z
  dsimp only [Function.comp_apply] at *
  dsimp
  by_cases h : Real.toNNReal z.1 < ρ z.2
  · simp only [if_pos h]
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  · simp [h]
