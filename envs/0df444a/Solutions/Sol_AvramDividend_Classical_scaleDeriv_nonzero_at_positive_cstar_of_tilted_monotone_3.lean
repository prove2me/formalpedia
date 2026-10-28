-- Prove2me | solution 3 for AvramDividend.Classical.scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:21:22.758988+00:00
-- url     : https://prove2.me/submissions/098d9834-5cb7-4903-b15a-72e0ecc4ac22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_standing
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
  obtain ⟨φ, hφ, htiltφ⟩ := htilt
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    scaleDeriv_continuous_of_standing X hX q hq W hW
  have hfinite : cstar W < ⊤ :=
    cstar_finite_of_normalized_monotone W φ hφ
      (hpos 1 (by norm_num)) htiltφ hdiff hcont
  have hcReal : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos hc.ne' hfinite.ne
  exact scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
    X hX q hq W hW hcReal hpos hdiff ⟨φ, hφ, htiltφ⟩
