-- Prove2me | solution 1 for AvramDividend.Classical.psi_eventually_gt_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:22:55.455871+00:00
-- url     : https://prove2.me/submissions/b750a841-bb6e-4be7-9c72-4064149bc206

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_boundedVariation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by
  -- The parameter bridges of the platform, in the two cases that the
  -- definition of `X.BoundedVariation` separates.  `X.BoundedVariation` is
  -- exactly `X.sigma = 0` together with a finite first moment of the small
  -- jumps, so a process that does not have bounded variation either has a
  -- positive Gaussian coefficient or an infinite first moment of the small
  -- jumps.
  by_cases hbv : X.BoundedVariation
  · exact psi_eventually_gt_of_boundedVariation X hX hbv q hq
  · by_cases hσ0 : X.σ = 0
    · have hnotmom : ¬(∫⁻ y in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal |y| ∂X.ν < ⊤) := by
        intro hlt
        exact hbv ⟨hσ0, hlt⟩
      have htop : (∫⁻ y in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
        refine le_antisymm (by simp) ?_
        by_contra hle
        exact hnotmom (lt_of_not_ge hle)
      exact psi_eventually_gt_of_infinite_small_jump_moment X hσ0 htop q hq
    · exact psi_eventually_gt_of_gaussian X q
        (lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ0))
