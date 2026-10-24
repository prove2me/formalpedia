-- Prove2me | solution 4 for AvramDividend.Classical.scaleFunction_contDiff_one_gaussian_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:02:14.085328+00:00
-- url     : https://prove2.me/submissions/c438722a-c35c-4d97-8c62-f4a99da7b7e7

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_positive_gaussian_without_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  obtain ⟨φ, hφ, hroot⟩ := positive_esscher_root_of_gaussian X q hq hσ
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hVeq : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x := by
    intro x hx
    rfl
  have hVc1 : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    esscher_tilted_scale_C1_of_positive_gaussian_without_standing
      X q hq W hW hσ φ hφ hroot V hVeq
  have hExp : ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (φ * x))
      (Ioi (0 : ℝ)) := by
    fun_prop
  have hprod : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (φ * x) * V x)
      (Ioi (0 : ℝ)) := hExp.mul hVc1
  apply hprod.congr
  intro x hx
  dsimp [V]
  have he : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    W x = 1 * W x := (one_mul _).symm
    _ = (Real.exp (φ * x) * Real.exp (-(φ * x))) * W x := by rw [he]
    _ = Real.exp (φ * x) * (Real.exp (-(φ * x)) * W x) := by ring
