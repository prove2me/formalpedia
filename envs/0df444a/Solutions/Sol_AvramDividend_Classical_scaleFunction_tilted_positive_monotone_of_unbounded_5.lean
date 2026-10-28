-- Prove2me | solution 5 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_unbounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:43:01.587769+00:00
-- url     : https://prove2.me/submissions/b35063f9-47fa-4b00-a5a8-00a2377440cc
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
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hbv
  obtain ⟨φ, μ, hφ, hnull, hfin, hcont, hexp⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hbv
  refine ⟨hpos, φ, hφ, ?_⟩
  have hm : MonotoneOn
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) := by
    apply excursion_integrated_tilted_scale_monotone W
      (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      φ μ hcont hpos hexp
    intro x hx
    rfl
  simpa only [neg_mul] using hm
