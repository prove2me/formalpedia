-- Prove2me | solution 1 for FeynmanKac.discounted_gradient_abs_le_space_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T10:22:45.854779+00:00
-- url     : https://prove2.me/submissions/01432cad-15bf-4e46-b090-ee76a1e97dae

import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Theorems.Thm_FeynmanKac_model_pathDiscount_pos_le_one
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (ω : Ω) (r : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) (m.terminalTime - m.initialTime))
    (hInt : IntervalIntegrable
      (fun z => m.potential (m.path z ω) z)
      MeasureTheory.volume m.initialTime (m.initialTime + r)) :
    |m.discountedGradientIntegrand u ω r| ≤
      |m.spaceGradientIntegrand u ω r| := by
  have hts : m.initialTime ≤ m.initialTime + r := by
    have hr0 := hr.1
    linarith
  obtain ⟨hpos, hle⟩ :=
    FeynmanKac.model_pathDiscount_pos_le_one P m (m.initialTime + r)
      hts ω hInt
  change |m.pathDiscount (m.initialTime + r) ω *
      m.spaceGradientIntegrand u ω r| ≤
      |m.spaceGradientIntegrand u ω r|
  rw [abs_mul, abs_of_pos hpos]
  calc
    m.pathDiscount (m.initialTime + r) ω *
        |m.spaceGradientIntegrand u ω r| ≤
          1 * |m.spaceGradientIntegrand u ω r| :=
      mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = |m.spaceGradientIntegrand u ω r| := one_mul _
