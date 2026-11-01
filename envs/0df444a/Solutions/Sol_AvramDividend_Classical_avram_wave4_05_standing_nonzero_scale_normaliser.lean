-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_standing_nonzero_scale_normaliser
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:40:32.160984+00:00
-- url     : https://prove2.me/submissions/90b799dd-f072-4f68-8d9e-77068b4cc7dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Standing scale regularity and Esscher monotonicity fix the barrier denominator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
  obtain ⟨hpos, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hC1 := scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  exact scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
    X hX q hq W hW hc hpos hdiff htilt
