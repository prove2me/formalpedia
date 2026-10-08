-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_unrestricted_verification_regularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:24:49.404521+00:00
-- url     : https://prove2.me/submissions/19f859ba-fefb-40cb-bf88-8696d2102526
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_zero_basic_verification_boundary
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_global_smooth_of_positive_cstar

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
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      (∀ y < 0, vcstar W y = 0) ∧
      ((¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) ∧
       (X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) (Ioi 0))) := by
  by_cases hc0 : cstar W = 0
  · obtain ⟨hcont, hnonneg, hneg⟩ :=
      vcstar_zero_basic_verification_boundary X hX q hq W hW hc0
    have hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0) :=
      vcstar_smooth_of_zero_cstar W hc0
    refine ⟨hcont, hnonneg, hneg, ?_⟩
    constructor
    · intro _
      exact hC2
    · intro _
      exact hC2.of_le (by norm_num)
  · have hcpos : 0 < cstar W :=
      lt_of_le_of_ne bot_le (Ne.symm hc0)
    obtain ⟨hcont, hnonneg, hneg⟩ :=
      vcstar_basic_boundary_regular_of_positive_cstar
        X hX q hq W hW hc hcpos
    obtain ⟨hC2, hC1⟩ :=
      vcstar_global_smooth_of_positive_cstar
        X hX q hq W hW hc hcpos h_smooth
    exact ⟨hcont, hnonneg, hneg, ⟨hC2, hC1⟩⟩
