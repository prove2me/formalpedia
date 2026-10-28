-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:46:16.467738+00:00
-- url     : https://prove2.me/submissions/4d34bc65-4d67-462c-9bf1-6b6e04440601
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integrated_tilted_scale_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  obtain ⟨φ, μ, hφ, hnull, hfin, hcont, hexp⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  refine ⟨hpos, φ, hφ, ?_⟩
  have hm : MonotoneOn
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) := by
    apply excursion_integrated_tilted_scale_monotone W
      (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      φ μ hcont hpos hexp
    intro x hx
    rfl
  simpa only [neg_mul] using hm
