-- Prove2me | solution 1 for AvramDividend.Classical.bv_tilted_kernel_contractive_parameter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:57:51.918054+00:00
-- url     : https://prove2.me/submissions/cb858aca-4cea-4e10-a67e-d6d318ab44ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_renewal_kernel_contractivity_of_standing
import Theorems.Thm_AvramDividend_Classical_positive_tilted_kernel_contractivity_of_discount_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ,
      let t : ℝ := (n : ℝ) + 1
      let a : ℝ := q / X.drift
      let s : ℝ := t - a
      0 < s ∧
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-(s + a) * (z : ℝ))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
          ENNReal.ofReal X.drift := by
  have hδ : 0 < X.drift := by
    have hnot : ¬ X.drift ≤ 0 := by
      intro hnon
      exact hX.1 ⟨hbv, Or.inl hnon⟩
    exact lt_of_not_ge hnot
  rcases bv_renewal_kernel_contractivity_of_standing X hX hbv q hq with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have ht : 0 < (n : ℝ) + 1 := by positivity
  simpa using
    (positive_tilted_kernel_contractivity_of_discount_bound
      (X.ν.map (fun y : ℝ => Real.toNNReal (-y)))
      X.drift q ((n : ℝ) + 1) hδ hq ht hn)
