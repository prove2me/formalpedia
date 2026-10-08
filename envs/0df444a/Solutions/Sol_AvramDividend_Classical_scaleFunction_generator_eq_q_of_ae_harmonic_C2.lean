-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_harmonic_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:33:36.588859+00:00
-- url     : https://prove2.me/submissions/18ff71b6-734c-4274-b2c2-b4ece367a628

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C2
import Theorems.Thm_AvramDividend_Classical_continuousOn_open_interval_of_compact_subintervals
import Theorems.Thm_AvramDividend_Classical_continuousOn_zero_of_ae_zero_restrict_open

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by
  let R : ℝ → ℝ := fun x => X.generator W x - q * W x
  have hcompact : ∀ l u : ℝ, 0 < l → l < u → u < a →
      ContinuousOn R (Icc l u) := by
    intro l u hl hlu hu
    rcases hbranch with hz | hbv
    · exact generator_residual_continuousOn_compact_of_zero_origin_C2
        X q W hW hz a l u hl hlu hu hC2
    · exact generator_residual_continuousOn_compact_of_standing_bv_C2
        X hX hbv q W hW a l u hl hlu hu hC2
  have hcont : ContinuousOn R (Ioo 0 a) :=
    continuousOn_open_interval_of_compact_subintervals
      R a ha hcompact
  exact continuousOn_zero_of_ae_zero_restrict_open
    volume (Ioo 0 a) isOpen_Ioo R hcont hae
