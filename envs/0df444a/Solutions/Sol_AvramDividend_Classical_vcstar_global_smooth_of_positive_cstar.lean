-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_global_smooth_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:24:05.317317+00:00
-- url     : https://prove2.me/submissions/6325caba-4754-4837-b73a-1371a6bc4132
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_positive_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) ∧
    (X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) (Ioi 0)) := by
  constructor
  · intro hnbv
    rcases h_smooth with hσ | hbv | hC2
    · exact vcstar_global_C2_gaussian_positive_barrier
        X hX q hq W hW hc hcpos hσ
    · exact False.elim (hnbv hbv)
    · exact hC2
  · intro hbv
    exact vcstar_global_C1_bv_positive_barrier
      X hX q hq W hW hc hcpos hbv
