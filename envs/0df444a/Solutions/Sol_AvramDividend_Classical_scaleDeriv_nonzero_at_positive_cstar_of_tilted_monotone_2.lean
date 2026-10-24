-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:01:21.875011+00:00
-- url     : https://prove2.me/submissions/d8899876-72da-4313-b1d5-6df236a32715
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Canonical C1 scale regularity and an increasing positive exponential
tilt give a finite positive barrier, hence a nonzero normaliser. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one X hX q hq W hW
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  obtain ⟨φ, hφ, htiltφ⟩ := htilt
  have hfinite : cstar W < ⊤ :=
    cstar_finite_of_normalized_monotone W φ hφ
      (hpos 1 (by norm_num)) htiltφ hdiff hcont
  have hcReal : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hc) (ne_of_lt hfinite)
  exact scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
    X hX q hq W hW hcReal hpos hdiff ⟨φ, hφ, htiltφ⟩
