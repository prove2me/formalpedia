-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_generator_cap_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:16:43.109989+00:00
-- url     : https://prove2.me/submissions/ca3d6697-51e6-4909-9934-7f8b12f43d05

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Interior source q-harmonicity reaches a positive cap through residual continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)))
    (a : ℝ) (ha : 0 < a)
    (hinterior : ∀ x ∈ Ioo (0 : ℝ) a,
      X.generator W x - q * W x = 0) :
    X.generator W a - q * W a = 0 := by
  let f : ℝ → ℝ := fun x => X.generator W x - q * W x
  have hcont : ContinuousOn f (Ioi (0 : ℝ)) := by
    simpa only [f] using
      (generator_residual_continuousOn_Ioi_of_zero_origin_C2
        X q W hW hzero hC2)
  have hinner : EqOn f (fun _ : ℝ => (0 : ℝ)) (Ioo (0 : ℝ) a) := by
    intro x hx
    exact hinterior x hx
  have hsubset : Ioo (0 : ℝ) a ⊆ Ioc (0 : ℝ) a := by
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  have hclosure : Ioc (0 : ℝ) a ⊆ closure (Ioo (0 : ℝ) a) := by
    rw [closure_Ioo (ne_of_lt ha)]
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hcontCap : ContinuousOn f (Ioc (0 : ℝ) a) :=
    hcont.mono (by intro x hx; exact hx.1)
  have hEqCap := hinner.of_subset_closure hcontCap
    continuousOn_const hsubset hclosure
  simpa only [f] using hEqCap ⟨ha, le_refl a⟩
