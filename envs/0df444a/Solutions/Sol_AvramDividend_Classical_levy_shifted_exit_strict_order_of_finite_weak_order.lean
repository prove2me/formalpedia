-- Prove2me | solution 1 for AvramDividend.Classical.levy_shifted_exit_strict_order_of_finite_weak_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:48:19.898224+00:00
-- url     : https://prove2.me/submissions/973ab3df-40f3-4a32-876b-4ba2e99a8408

import Mathlib.Topology.Order.LeftRightNhds
import Theorems.Thm_AvramDividend_Classical_levy_shiftedIncrements_rightContinuous
import Theorems.Thm_AvramDividend_Classical_separated_strict_passage_infima_no_finite_tie
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Exclude finite simultaneous first exits by right continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (lower upper : ℝ) (hsep : lower < upper)
    (hFinite : (⨅ (s : ℝ≥0)
        (_ : upper < X.X (u + s) ω - X.X u ω),
        (s : ℝ≥0∞)) ≠ ⊤)
    (hLe :
      (⨅ (s : ℝ≥0)
        (_ : upper < X.X (u + s) ω - X.X u ω),
        (s : ℝ≥0∞)) ≤
      (⨅ (s : ℝ≥0)
        (_ : X.X (u + s) ω - X.X u ω < lower),
        (s : ℝ≥0∞))) :
    (⨅ (s : ℝ≥0)
      (_ : upper < X.X (u + s) ω - X.X u ω),
      (s : ℝ≥0∞)) <
    (⨅ (s : ℝ≥0)
      (_ : X.X (u + s) ω - X.X u ω < lower),
      (s : ℝ≥0∞)) := by
  classical
  let U : ℝ≥0∞ := ⨅ (s : ℝ≥0)
    (_ : upper < X.X (u + s) ω - X.X u ω), (s : ℝ≥0∞)
  let D : ℝ≥0∞ := ⨅ (s : ℝ≥0)
    (_ : X.X (u + s) ω - X.X u ω < lower), (s : ℝ≥0∞)
  change U ≠ ⊤ at hFinite
  change U ≤ D at hLe
  change U < D
  apply lt_of_le_of_ne hLe
  intro heq
  have hcast : ((U.toNNReal : ℝ≥0) : ℝ≥0∞) = U :=
    ENNReal.coe_toNNReal hFinite
  have hUp : ((U.toNNReal : ℝ≥0) : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : upper < X.X (u + s) ω - X.X u ω),
        (s : ℝ≥0∞)) := hcast
  have hDown : ((U.toNNReal : ℝ≥0) : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : X.X (u + s) ω - X.X u ω < lower),
        (s : ℝ≥0∞)) := hcast.trans heq
  exact separated_strict_passage_infima_no_finite_tie
    (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω)
    U.toNNReal lower upper hsep
    (levy_shiftedIncrements_rightContinuous X ω u U.toNNReal)
    hUp hDown
