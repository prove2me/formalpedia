-- Prove2me | solution 4 for AvramDividend.Classical.vcstar_deriv_ge_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:01:46.97946+00:00
-- url     : https://prove2.me/submissions/9d36303e-1d52-4e11-b0e8-c650fefd9bfc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_cstar_finite_zero_or_deriv_minimal
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    AvramDividend.Classical.scaleFunction_contDiff_one X hX q hq W hW
  have hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    AvramDividend.Classical.scaleDeriv_pos X hX q hq W hW
  have hmin :
      (cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x) :=
    (AvramDividend.Classical.cstar_finite_zero_or_deriv_minimal
      X hX q hq W hW).2
  exact AvramDividend.Classical.vcstar_deriv_ge_one_of_regular_minimal
    W hreg hpos hmin
