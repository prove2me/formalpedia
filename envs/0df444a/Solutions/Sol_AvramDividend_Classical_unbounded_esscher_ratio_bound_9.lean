-- Prove2me | solution 9 for AvramDividend.Classical.unbounded_esscher_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:14:29.544382+00:00
-- url     : https://prove2.me/submissions/2144e46a-18b7-4dba-b777-6e9a8a91bc02

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

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
  refine ⟨φ, hφ, hroot, fun x y hx hxy => ?_⟩
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hpos : 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv y hy
  have hdecay : W x ≤ Real.exp (-(φ * (y - x))) * W y :=
    unbounded_esscher_root_first_passage_scale_decay X q hq W hW hnbv φ hφ hroot x y hx hxy
  exact (div_le_iff₀ hpos).mpr hdecay
