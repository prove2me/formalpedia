-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_interior_harmonicity_of_scale_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:18:24.561213+00:00
-- url     : https://prove2.me/submissions/15be1be3-e728-44f3-b707-6c676a68d310

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_congr_scaledW_inside_cstar
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hscale : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
  let a : ℝ := (cstar W).toReal
  let k : ℝ := (deriv W a)⁻¹
  let g : ℝ → ℝ := fun z => divE (W z) (scaleDeriv W a)
  have hg : g = fun z => k * W z := by
    funext z
    have ha0 : a ≠ 0 := ne_of_gt ha
    simp [g, k, divE, scaleDeriv, ha0, div_eq_mul_inv, mul_comm]
  intro x hx
  obtain ⟨hdomW, hharmW⟩ := hscale x hx
  have hdomg : X.GeneratorIntegrable g x := by
    rw [hg]
    exact levy_generatorIntegrable_const_mul X W k x hdomW
  have hgen : X.generator g x = k * X.generator W x := by
    rw [hg]
    exact levy_generator_const_mul X W k x
  have hval : vcstar W x = g x :=
    vcstar_eq_scaledW_le_cstar_of_support
      W hW.1 x (le_of_lt hx.2)
  have hcomp := vcstar_generator_congr_scaledW_inside_cstar
    X q W hW x hx
  change (X.GeneratorIntegrable (vcstar W) x ↔
      X.GeneratorIntegrable g x) ∧
      X.generator (vcstar W) x = X.generator g x at hcomp
  obtain ⟨hiff, heq⟩ := hcomp
  refine ⟨hiff.mpr hdomg, ?_⟩
  rw [heq, hgen, hval, congrFun hg x]
  calc
    k * X.generator W x - q * (k * W x) =
        k * (X.generator W x - q * W x) := by ring
    _ = 0 := by rw [hharmW]; ring
