-- Prove2me | solution 4 for AvramDividend.Classical.unbounded_esscher_ratio_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:35:43.818611+00:00
-- url     : https://prove2.me/submissions/ee4835e0-b6bb-4891-a094-7d8efb41c073
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Obtain the scale ratio estimate from the root-specific decay statement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  refine ⟨φ, hφ, hroot, ?_⟩
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hWy : 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv y hy
  have hdecay :=
    unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot x y hx hxy
  exact (div_le_iff₀ hWy).2 (by simpa only [mul_comm] using hdecay)
