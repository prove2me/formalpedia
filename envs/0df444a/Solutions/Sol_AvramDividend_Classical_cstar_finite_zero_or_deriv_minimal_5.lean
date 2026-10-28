-- Prove2me | solution 5 for AvramDividend.Classical.cstar_finite_zero_or_deriv_minimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:09:32.211981+00:00
-- url     : https://prove2.me/submissions/256a083c-a406-4dd3-aff8-78d1c5a3ab1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The finite optimal barrier is zero or a positive derivative minimiser. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ((cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x →
            deriv W (cstar W).toReal ≤ deriv W x)) := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl _)
  exact ⟨cstar_lt_top X hX q hq W hW,
    cstar_toReal_zero_or_minimal_of_deriv_continuous W hcont⟩
