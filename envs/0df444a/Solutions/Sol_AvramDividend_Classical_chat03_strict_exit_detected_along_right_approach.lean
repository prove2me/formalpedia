-- Prove2me | solution 1 for AvramDividend.Classical.chat03_strict_exit_detected_along_right_approach
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:41:05.847774+00:00
-- url     : https://prove2.me/submissions/4497f42a-b728-4941-8b90-85d6641d4180

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_two_sided_exit_right_eventually
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Any sequence of sample times converging to a strict exit from the right
detects that exit eventually. This transfers the exact proved Lévy
right-persistence lemma to sampled path times.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower upper : ℝ)
    (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici t] t))
    (h : X.X t ω < lower ∨ upper < X.X t ω) :
    ∀ᶠ n in atTop,
      X.X (clock n) ω < lower ∨ upper < X.X (clock n) ω := by
  exact hclock.eventually
    (chat03_strict_two_sided_exit_right_eventually X ω t lower upper h)