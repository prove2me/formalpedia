-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:26:14.009994+00:00
-- url     : https://prove2.me/submissions/8a766a0f-f724-4638-bd58-15d8d986785a

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/--
For every original sample path and every positive time, the true nonzero
negative jump of X is exactly a strict upward jump of its drift residual.
No bounded-variation or finite-intensity assumption is needed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (Function.leftLim
        (fun u : ℝ≥0 => (u : ℝ) * X.drift - X.X u ω) t <
      (t : ℝ) * X.drift - X.X t ω) ↔
    X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0 := by
  letI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  have hlin :
      Tendsto (fun u : ℝ≥0 => (u : ℝ) * X.drift)
        (𝓝[<] t) (𝓝 ((t : ℝ) * X.drift)) :=
    (NNReal.continuous_coe.mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hleftY :
      Function.leftLim
        (fun u : ℝ≥0 => (u : ℝ) * X.drift - X.X u ω) t =
        (t : ℝ) * X.drift - l :=
    leftLim_eq_of_tendsto (hlin.sub hl)
  have hleftX :
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = l :=
    leftLim_eq_of_tendsto hl
  have hnonpos :=
    avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω t ht
  rw [hleftX] at hnonpos
  rw [hleftY, hleftX]
  constructor
  · intro h
    have hneg : X.X t ω - l < 0 := by linarith
    exact ne_of_lt hneg
  · intro hne
    have hneg : X.X t ω - l < 0 := by
      by_contra hn
      have hge : 0 ≤ X.X t ω - l := le_of_not_gt hn
      have hz : X.X t ω - l = 0 := le_antisymm hnonpos hge
      exact hne hz
    linarith
