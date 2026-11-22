-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_scale_pos_no_standing_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:25:01.162279+00:00
-- url     : https://prove2.me/submissions/5c8ff27a-dd65-4a4b-bc62-bb0d7b63d30c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_eventual_psi_above_no_standing_public
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_psi_quadratic_upper_no_standing_public
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_scale_origin_pos_no_standing_public

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (hx0 : 0 ≤ x) :
    0 < W x := by
  obtain ⟨β0, hβ0, hψevent⟩ := p2m81_bv_root_eventual_psi_above_no_standing_public X q φ hq hφ hroot hBV
  have hquad : ∀ θ : ℝ, β0 ≤ θ → X.ψ θ - q ≤ (|X.drift| + |q|) * (1 + θ ^ 2) := fun θ hθ =>
    p2m81_bv_root_psi_quadratic_upper_no_standing_public X q φ hq hφ hroot hBV θ (le_trans hβ0 hθ)
  have hpos := scaleFunction_strict_pos_of_eventual_psi_bound X q W hW β0 (|X.drift| + |q|) hβ0 hψevent hquad
  rcases eq_or_lt_of_le hx0 with hZero | hPos
  · subst hZero
    exact p2m81_bv_root_scale_origin_pos_no_standing_public X q φ hq hφ hroot W hW hBV
  · exact hpos x hPos
