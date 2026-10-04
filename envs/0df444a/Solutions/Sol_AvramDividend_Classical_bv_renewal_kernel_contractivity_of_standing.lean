-- Prove2me | solution 1 for AvramDividend.Classical.bv_renewal_kernel_contractivity_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T08:17:01.532927+00:00
-- url     : https://prove2.me/submissions/224931fe-91c7-48fc-8883-038eb557bb0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_positive_jump_moment_finite
import Theorems.Thm_AvramDividend_Classical_discounted_renewal_kernel_mass_small
open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ,
      ENNReal.ofReal (q / ((n : ℝ) + 1)) +
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
              ((n : ℝ) + 1))
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
        ENNReal.ofReal X.drift := by
  have hδ : 0 < X.drift := by
    have hnot : ¬ X.drift ≤ 0 := by
      intro hnon
      exact hX.1 ⟨hbv, Or.inl hnon⟩
    exact lt_of_not_ge hnot
  exact discounted_renewal_kernel_mass_small
    (X.ν.map (fun y : ℝ => Real.toNNReal (-y)))
    (bv_positive_jump_moment_finite X hbv)
    q X.drift hq hδ
