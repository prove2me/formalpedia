-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_crossing_weighted_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:51:12.528325+00:00
-- url     : https://prove2.me/submissions/085c3d9f-f74b-441c-8237-267140ecedac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_source_crossing_quadratic_strip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine Gaussian Lévy crossing strip stays quadratic under any nonnegative exponential discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ θ : ℝ, 0 ≤ θ →
      ∀ y : ℝ, -1 < y → y < 0 →
        IntegrableOn
          (fun x : ℝ => Real.exp (-(θ * x)) *
            |SpectrallyNegativeLevy.generatorIntegrand W x y|)
          (Ioo (0 : ℝ) (-y)) ∧
        (∫ x in Ioo (0 : ℝ) (-y),
          Real.exp (-(θ * x)) *
            |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤
          C * y ^ 2 := by
  obtain ⟨C, hC, hstrip⟩ :=
    avram_wave3_05_gaussian_source_crossing_quadratic_strip
      X hX q hq W hW hσ
  refine ⟨C, hC, ?_⟩
  intro θ hθ y hy1 hy
  obtain ⟨hint, hbound⟩ := hstrip y hy1 hy
  have hA : MeasurableSet (Ioo (0 : ℝ) (-y)) := measurableSet_Ioo
  have hsub : Ioo (0 : ℝ) (-y) ⊆ Icc (0 : ℝ) (-y) := by
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hExp : ContinuousOn
      (fun x : ℝ => Real.exp (-(θ * x))) (Icc (0 : ℝ) (-y)) := by
    fun_prop
  have hint' : IntegrableOn
      (fun x : ℝ => |SpectrallyNegativeLevy.generatorIntegrand W x y| *
        Real.exp (-(θ * x))) (Ioo (0 : ℝ) (-y)) :=
    hint.mul_continuousOn_of_subset hExp hA isCompact_Icc hsub
  have hintw : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x y|)
      (Ioo (0 : ℝ) (-y)) := by
    simpa only [mul_comm] using hint'
  refine ⟨hintw, ?_⟩
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) (-y),
      Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
      |SpectrallyNegativeLevy.generatorIntegrand W x y| := by
    intro x hx
    have htx : 0 ≤ θ * x := mul_nonneg hθ hx.1.le
    have hexp : Real.exp (-(θ * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hexp (abs_nonneg _))
  exact (setIntegral_mono_on hintw hint hA hpoint).trans hbound
