-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_log_derivative_nonintegrable_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:50:11.474985+00:00
-- url     : https://prove2.me/submissions/34163d65-7199-4cf4-ac43-d14bab9aee86

import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_log_derivative_nonintegrable_of_positive_vanishing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hVdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x) :
    ¬ IntegrableOn (fun y : ℝ => deriv V y / V y) (Ioi (0 : ℝ)) := by
  have hWzero : W 0 = 0 := by
    by_cases hσ : 0 < X.σ
    · exact scaleFunction_zero_origin_gaussian_without_standing
        X q hq W hW hσ
    · have hσzero : X.σ = 0 :=
        le_antisymm (le_of_not_gt hσ) X.σ_nonneg
      rcases unbounded_variation_gaussian_or_infinite_small_jump_moment
        X hnbv with hg | hj
      · exact False.elim (hσ hg)
      · exact scaleFunction_zero_origin_infinite_small_jumps
          X hσzero hj q hq W hW
  have hWpos : ∀ y : ℝ, 0 < y → 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hVpos : ∀ y : ℝ, 0 < y → 0 < V y := by
    intro y hy
    rw [hV y hy]
    exact mul_pos (Real.exp_pos _) (hWpos y hy)
  have hWcont : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hWzero
  have hprod : Continuous
      (fun y : ℝ => Real.exp (-(φ * y)) * W y) := by
    fun_prop
  have hprodlim : Tendsto
      (fun y : ℝ => Real.exp (-(φ * y)) * W y)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (hprod.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simpa [hWzero] using h
  have hVeq : V =ᶠ[𝓝[>] (0 : ℝ)]
      (fun y : ℝ => Real.exp (-(φ * y)) * W y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hV y hy
  have hVzero : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hprodlim.congr' hVeq.symm
  exact log_derivative_nonintegrable_of_positive_vanishing
    V hVpos hVdiff hVzero
