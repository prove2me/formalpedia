-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_left_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:58:49.456766+00:00
-- url     : https://prove2.me/submissions/b94876a1-9eeb-48ce-a0c2-13b31af3f379

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_monotone_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- After removing each actual original BV negative left jump, the genuine
physical-drift residual has no left jumps at positive times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim (fun s : ℝ≥0 =>
        (((s : ℝ) * X.drift - X.X s ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) t = (((t : ℝ) * X.drift - X.X t ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict X hBV,
     avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split X hBV,
     avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV,
     avram_p3_a_bvdrift_original_real_jump_total_monotone_time X hBV]
    with ω hleft hsplit hraw hmono
  intro t ht
  let J : ℝ≥0 → ℝ := fun s =>
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)
  let Jpos : ℝ≥0 → ℝ := fun s =>
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
      ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω) else 0).toReal
  have hJeq : ∀ s : ℝ≥0, Jpos s = J s := by
    intro s
    exact (hraw 0 s (show (0 : ℝ≥0) ≤ s from zero_le)).2
  have hJmono : Monotone J := by
    intro s r hsr
    have h := hmono hsr
    change Jpos s ≤ Jpos r at h
    rw [hJeq s, hJeq r] at h
    exact h
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hJtendsto : Tendsto J (𝓝[<] t) (nhds (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by
    have h := hJmono.tendsto_leftLim t
    rw [show Function.leftLim J t = (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) from hleft t ht] at h
    exact h
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  have hXleft : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = l :=
    leftLim_eq_of_tendsto hl
  have hXtendsto : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t)
      (nhds (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)) := by
    rw [hXleft]
    exact hl
  have htime : Tendsto (fun s : ℝ≥0 => (s : ℝ) * X.drift)
      (𝓝[<] t) (nhds ((t : ℝ) * X.drift)) :=
    ((NNReal.continuous_coe.mul continuous_const).tendsto t).mono_left
      nhdsWithin_le_nhds
  have hRleft :
      Function.leftLim (fun s : ℝ≥0 =>
        (((s : ℝ) * X.drift - X.X s ω) - J s)) t =
        (((t : ℝ) * X.drift -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) - (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) :=
    leftLim_eq_of_tendsto ((htime.sub hXtendsto).sub hJtendsto)
  have hendpoint : J t =
      (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - X.X t ω) +
        (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := hsplit t ht
  change Function.leftLim (fun s : ℝ≥0 =>
    (((s : ℝ) * X.drift - X.X s ω) - J s)) t =
      (((t : ℝ) * X.drift - X.X t ω) - J t)
  rw [hRleft, hendpoint]
  ring
