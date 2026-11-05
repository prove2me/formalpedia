-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_killed_terminal_eventual_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:42:30.199201+00:00
-- url     : https://prove2.me/submissions/89adda9c-e3d7-492e-a975-6865ef56f0ab

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Strict killing preserves an eventual lower bound at the ruin horizon,
even though ordinary continuity may fail when ruin happens exactly then. -/
theorem solution
    (r : ℝ≥0∞) (F : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hpos : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < r → 0 ≤ F s)
    (hcont : (t : ℝ≥0∞) < r → Tendsto F (𝓝[<] t) (𝓝 (F t)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
      (if (t : ℝ≥0∞) < r then F t else 0) - ε <
      (if (s : ℝ≥0∞) < r then F s else 0) := by
  by_cases hSurv : (t : ℝ≥0∞) < r
  · have hBelow : F t - ε < F t := sub_lt_self _ hε
    have hLive : ∀ᶠ s in 𝓝[<] t, F t - ε < F s :=
      (hcont hSurv).eventually (Ioi_mem_nhds hBelow)
    filter_upwards [hLive, self_mem_nhdsWithin] with s hsValue hsLt
    have hst : s < t := Set.mem_Iio.mp hsLt
    have hEarlier : (s : ℝ≥0∞) < r := by
      have hcoe : (s : ℝ≥0∞) < (t : ℝ≥0∞) := by exact_mod_cast hst
      exact lt_trans hcoe hSurv
    simpa [hSurv, hEarlier] using hsValue
  · have hId : Tendsto (fun s : ℝ≥0 => s) (𝓝[<] t) (𝓝 t) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hNearPos : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, 0 < s :=
      hId.eventually (Ioi_mem_nhds ht)
    filter_upwards [hNearPos] with s hspos
    have hKilledNonneg : 0 ≤ (if (s : ℝ≥0∞) < r then F s else 0) := by
      split_ifs with hEarlier
      · exact hpos s hspos hEarlier
      · exact le_refl _
    have hSmall : (0 : ℝ) - ε < 0 := by linarith
    simpa [hSurv] using lt_of_lt_of_le hSmall hKilledNonneg
