-- Prove2me | solution 10 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:01:43.517624+00:00
-- url     : https://prove2.me/submissions/73d07e96-5d1a-415e-8244-c08957da6a28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_three_branch_regularity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hTilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x)
        (Ioi (0 : ℝ)) :=
    (scaleFunction_tilted_positive_monotone X hX q hq W hW).2
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hGaussian : 0 < X.σ →
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ =>
          Real.exp (-φ * x) * W x) (Ioi (0 : ℝ)) :=
    fun _ => hTilt
  have hBV : X.BoundedVariation →
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    fun _ => hC1
  exact vcstar_deriv_one_of_three_branch_regularity
    X hX q hq W hW hc hcpos h_smooth hGaussian hBV
