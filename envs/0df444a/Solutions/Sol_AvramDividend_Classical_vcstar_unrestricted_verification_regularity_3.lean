-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_unrestricted_verification_regularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:42:44.517754+00:00
-- url     : https://prove2.me/submissions/58c7c2d5-6a8c-4d46-b9e3-71df4a85ecaf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_zero_basic_verification_boundary
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_positive_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Source-faithful global regularity package, conditional on Gaussian C2 gluing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      (∀ y < 0, vcstar W y = 0) ∧
      ((¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) ∧
       (X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) (Ioi 0))) := by
  by_cases hzero : cstar W = 0
  · obtain ⟨hcont, hnonneg, hneg⟩ :=
      vcstar_zero_basic_verification_boundary X hX q hq W hW hzero
    have hc2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0) :=
      vcstar_smooth_of_zero_cstar W hzero
    refine ⟨hcont, hnonneg, hneg, ?_, ?_⟩
    · intro _
      exact hc2
    · intro _
      exact hc2.of_le (by norm_num)
  · have hpos : 0 < cstar W := pos_iff_ne_zero.mpr hzero
    obtain ⟨hcont, hnonneg, hneg⟩ :=
      vcstar_basic_boundary_regular_of_positive_cstar
        X hX q hq W hW hc hpos
    refine ⟨hcont, hnonneg, hneg, ?_, ?_⟩
    · intro hnotBV
      rcases h_smooth with hσ | hbv | hC2
      · exact vcstar_global_C2_gaussian_positive_barrier
          X hX q hq W hW hc hpos hσ
      · exact False.elim (hnotBV hbv)
      · exact hC2
    · intro hbv
      exact vcstar_global_C1_bv_positive_barrier
        X hX q hq W hW hc hpos hbv
