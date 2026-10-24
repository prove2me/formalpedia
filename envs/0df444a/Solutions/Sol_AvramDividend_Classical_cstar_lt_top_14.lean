-- Prove2me | solution 14 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:32:48.037426+00:00
-- url     : https://prove2.me/submissions/79b3e36b-85b4-42bd-a7c0-5d68e66e0790
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_deriv_continuous_tendsto_atTop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Under q-scale C1 regularity, coercivity of its derivative forces the
optimal barrier to be finite by the proved deterministic compactness lemma.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact cstar_lt_top_of_deriv_continuous_tendsto_atTop
    W hcont (scaleDeriv_tendsto_atTop X hX q hq W hW)
