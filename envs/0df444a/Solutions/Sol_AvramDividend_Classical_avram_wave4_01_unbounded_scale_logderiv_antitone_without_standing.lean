-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_unbounded_scale_logderiv_antitone_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:19:32.20503+00:00
-- url     : https://prove2.me/submissions/45b15ba8-f289-42cb-a9c8-c7982df708d4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_log_concavity_core
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_unbounded_variation_C1_without_standing
import Theorems.Thm_AvramDividend_Classical_log_derivative_antitone_of_concave_log
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original first-record hazard is the decreasing logarithmic slope
of the positive q-scale function, in every unbounded-variation branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    AntitoneOn
      (fun x : ℝ => deriv W x / W x)
      (Set.Ioi (0 : ℝ)) := by
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hconcave :
      ConcaveOn ℝ (Ioi (0 : ℝ))
        (fun z : ℝ => Real.log (W z)) :=
    unbounded_scale_log_concavity_core X q hq W hW hnbv
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    avram_wave4_01_unbounded_variation_C1_without_standing
      X q hq W hW hnbv
  have hderiv :
      ∀ x : ℝ, 0 < x →
        HasDerivAt W (W x * (deriv W x / W x)) x := by
    intro x hx
    have hpoint : ContDiffAt ℝ 1 W x :=
      hC1.contDiffAt (isOpen_Ioi.mem_nhds hx)
    have hd : HasDerivAt W (deriv W x) x :=
      (hpoint.differentiableAt (by norm_num)).hasDerivAt
    have heq : W x * (deriv W x / W x) = deriv W x := by
      field_simp [ne_of_gt (hpos x hx)]
    rw [heq]
    exact hd
  exact log_derivative_antitone_of_concave_log
    W (fun x : ℝ => deriv W x / W x) hpos hconcave hderiv
