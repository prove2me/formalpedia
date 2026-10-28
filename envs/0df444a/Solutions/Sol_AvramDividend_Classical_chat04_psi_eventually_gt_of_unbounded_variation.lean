-- Prove2me | solution 1 for AvramDividend.Classical.chat04_psi_eventually_gt_of_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:54:47.103589+00:00
-- url     : https://prove2.me/submissions/cdac057f-8918-4955-9ae4-4ee88b4ba02d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by
  by_cases hσzero : X.σ = 0
  · have hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
      by_contra hne
      have hfinite : (∫⁻ y in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal |y| ∂X.ν) < ⊤ :=
        lt_top_iff_ne_top.mpr hne
      exact hnbv ⟨hσzero, hfinite⟩
    exact psi_eventually_gt_of_infinite_small_jump_moment
      X hσzero hsmall q hq
  · have hσpos : 0 < X.σ :=
      lt_of_le_of_ne X.σ_nonneg (Ne.symm hσzero)
    exact psi_eventually_gt_of_gaussian X q hσpos
