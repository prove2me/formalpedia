-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_uncentered_jump_equals_centered_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:34:22.957093+00:00
-- url     : https://prove2.me/submissions/4d5358da-14e6-4b39-a32a-ef6b1dc603da

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.DenselyOrdered
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

/-- The canonical original jump and the centred-path jump are identical. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℝ≥0) (hu : 0 < u) :
    X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u =
      (X.X u ω - X.X 0 ω) -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u := by
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω - X.X 0 ω
  have hCenter :=
    (avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag X ω).2 u hu
  haveI : NeBot (𝓝[<] u) := nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  have hOriginal : Tendsto (fun t : ℝ≥0 => X.X t ω) (𝓝[<] u)
      (𝓝 (Function.leftLim Y u + X.X 0 ω)) := by
    simpa only [Y, sub_add_cancel] using hCenter.add_const (X.X 0 ω)
  have hLeft : Function.leftLim (fun t : ℝ≥0 => X.X t ω) u =
      Function.leftLim Y u + X.X 0 ω := by
    exact leftLim_eq_of_tendsto hOriginal
  dsimp [Y] at hLeft ⊢
  rw [hLeft]
  ring
