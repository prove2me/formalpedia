-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_jump_shifted_agreement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:46:20.873548+00:00
-- url     : https://prove2.me/submissions/a783dfcf-d1e2-45e5-a972-d36da7a0a9f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (w V : ℝ → ℝ) (C : ℝ≥0∞) (δ y : ℝ)
    (hδ : 0 < δ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hV : ∀ z : ℝ, ENNReal.ofReal z ≤ C → V z = w z) :
    ContDiffOn ℝ 2 V (Ioo 0 y) ∧
    (∀ r ∈ Icc (δ / 3) (2 * (δ / 3)), deriv V (y - r) = deriv w (y - r)) ∧
    (∀ r ∈ Icc (δ / 3) (2 * (δ / 3)), ∀ z ≤ 0,
      V (y + z - r) = w (y + z - r)) ∧
    (∀ r ∈ Icc (δ / 3) (2 * (δ / 3)), ∀ z < 0,
      SpectrallyNegativeLevy.generatorIntegrand V (y - r) z =
      SpectrallyNegativeLevy.generatorIntegrand w (y - r) z) := by 
  have he : EqOn V w (Ioo 0 y) := by
    intro t ht
    exact hV t ((ENNReal.ofReal_le_ofReal ht.2.le).trans hyC)
  have hs : Ioo 0 y ⊆ {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C} := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < y)).2 ht.2) hyC⟩
  have hd : ∀ r ∈ Icc (δ / 3) (2 * (δ / 3)),
      deriv V (y - r) = deriv w (y - r) := by
    intro r hr
    have hmem : y - r ∈ Ioo 0 y := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h := he.iteratedDeriv_of_isOpen isOpen_Ioo 1 hmem
    simpa only [iteratedDeriv_one] using h
  have hv : ∀ r ∈ Icc (δ / 3) (2 * (δ / 3)), ∀ z ≤ 0,
      V (y + z - r) = w (y + z - r) := by
    intro r hr z hz
    exact hV _ ((ENNReal.ofReal_le_ofReal (by linarith [hr.1] : y + z - r ≤ y)).trans hyC)
  refine ⟨(hw.mono hs).congr he, hd, hv, ?_⟩
  intro r hr z hz
  unfold SpectrallyNegativeLevy.generatorIntegrand
  have h0 := hv r hr 0 le_rfl
  have h1 := hv r hr z hz.le
  rw [show y - r + z = y + z - r by ring, h1, hd r hr]
  simpa only [add_zero] using congrArg (fun t =>
    w (y + z - r) - t - deriv w (y - r) * z *
      (Ioo (-1 : ℝ) 1).indicator 1 z) h0
