-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_contDiff_one_gaussian_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:30:34.929122+00:00
-- url     : https://prove2.me/submissions/245db88f-493b-4bf6-832f-f703140f3a15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_integrated_volterra_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_integrated_volterra_regularizes_C1

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
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_gaussian X q hq hσ
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x := by
    intro x hx
    rfl
  obtain ⟨a, β, K, ha, hKi, hVb, hEq⟩ :=
    gaussian_esscher_integrated_volterra_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV
  have hVc : ContinuousOn V (Ioi (0 : ℝ)) :=
    gaussian_esscher_tilted_scale_continuous
      X q hq W hW hσ φ V hV
  have hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    integrated_volterra_regularizes_C1 V K a β ha hKi hVc hVb hEq
  have he : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (φ * x)) (Ioi (0 : ℝ)) := by
    have hlin : ContDiff ℝ 1 (fun x : ℝ => φ * x) := by
      have hc : ContDiff ℝ 1 (fun _ : ℝ => (φ : ℝ)) := contDiff_const
      exact hc.mul contDiff_id
    exact (Real.contDiff_exp.comp hlin).contDiffOn
  have hp : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (φ * x) * V x) (Ioi 0) :=
    he.mul hVdiff
  apply hp.congr
  intro x hx
  change W x = Real.exp (φ * x) * V x
  rw [hV x hx]
  rw [← mul_assoc, ← Real.exp_add]
  simp
