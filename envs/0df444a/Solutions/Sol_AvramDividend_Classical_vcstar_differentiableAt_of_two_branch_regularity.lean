-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_differentiableAt_of_two_branch_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:25:04.070111+00:00
-- url     : https://prove2.me/submissions/d759097b-d5f1-45ed-844f-ed185658ae0a

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_three_branch_regularity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation)
    (hgauss : 0 < X.σ →
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hbv : X.BoundedVariation →
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ))) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by
  have hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
    rcases hregular with hσ | hvar
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hvar)
  have hv : deriv (vcstar W) (cstar W).toReal = 1 :=
    vcstar_deriv_one_of_three_branch_regularity
      X hX q hq W hW hc hcpos hsmooth hgauss hbv
  have hvne : deriv (vcstar W) (cstar W).toReal ≠ 0 := by
    rw [hv]
    exact one_ne_zero
  exact differentiableAt_of_deriv_ne_zero hvne
