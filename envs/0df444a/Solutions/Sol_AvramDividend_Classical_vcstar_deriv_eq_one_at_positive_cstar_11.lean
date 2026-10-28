-- Prove2me | solution 11 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:35:15.797342+00:00
-- url     : https://prove2.me/submissions/13486915-6e03-4792-8f8c-bee26b432590
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_three_branch_regularity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Smooth fit at a positive finite barrier from the three-branch transfer. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hgauss : 0 < X.σ →
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
    intro _
    exact (scaleFunction_tilted_positive_monotone X hX q hq W hW).2
  have hbv : X.BoundedVariation →
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
    intro _
    exact scaleFunction_contDiff_one_of_standing X hX q hq W hW
  exact vcstar_deriv_one_of_three_branch_regularity
    X hX q hq W hW hc hcpos h_smooth hgauss hbv
