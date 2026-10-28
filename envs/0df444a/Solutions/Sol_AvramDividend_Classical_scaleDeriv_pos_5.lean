-- Prove2me | solution 5 for AvramDividend.Classical.scaleDeriv_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:09:22.39175+00:00
-- url     : https://prove2.me/submissions/070ccc1c-5cb8-42d2-87ef-8b5e99985490
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  -- Derivative positivity via the tilted bridge: the tilted-monotone sketch
  -- supplies positivity and an Esscher tilt; C1-smoothness (Open) yields
  -- differentiability at every positive point; the Proved tilted-to-positive
  -- converter closes. Negation/export shapes verified against pinned sources.
  -- Principal lemma: scaleDeriv_pos_of_tilted_positive_monotone (Proved).
  -- Exact unresolved identities: tilted bridge 8d7288ac (sketch),
  -- contDiff_one 310bb0bc (Open).
  intro x hx
  obtain ⟨hpos, φ, hφ, hmono⟩ :=
    AvramDividend.Classical.scaleFunction_tilted_positive_monotone
      X hX q hq W hW
  have hD : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    AvramDividend.Classical.scaleFunction_contDiff_one_of_standing
      X hX q hq W hW
  have hdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y := by
    intro y hy
    exact (hD.differentiableOn one_ne_zero).differentiableAt
      (Ioi_mem_nhds hy)
  -- Bridge the tilted conclusion into the converter's hypothesis shape;
  -- `simpa` normalises both sides so either negation placement matches.
  have htilt : ∃ φ_ : ℝ, 0 < φ_ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ_ * x) * W x) (Ioi (0 : ℝ)) :=
    ⟨φ, hφ, by simpa only [neg_mul] using hmono⟩
  -- Repair (parent 14596, E01): the converter takes the full context
  -- (X hX q hq W hW) before (hpos hdiff htilt), not W first.
  exact AvramDividend.Classical.scaleDeriv_pos_of_tilted_positive_monotone
    X hX q hq W hW hpos hdiff htilt x hx
