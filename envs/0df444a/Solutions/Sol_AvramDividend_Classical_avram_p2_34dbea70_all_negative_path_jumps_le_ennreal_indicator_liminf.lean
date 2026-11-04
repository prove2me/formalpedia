-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:06:45.518199+00:00
-- url     : https://prove2.me/submissions/df08c8f5-c9c9-4ee5-8897-b723f85c065e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_index_indicator_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_enat_to_ennreal_liminf_commutes
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_enat_to_ennreal_indicator_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Preserve the full possibly infinite negative jump count under ENNReal grid conversion. -/
theorem solution (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε) :
    ENat.toENNReal S.encard ≤ Filter.liminf (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℝ≥0∞) else 0)) atTop := by
  let f : ℕ → ℕ∞ := fun n =>
    ∑ i ∈ Finset.range (n + 1),
      (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
        then (1 : ℕ∞) else 0)
  have hindex : S.encard ≤ Filter.liminf f atTop :=
    avram_p2_34dbea70_all_negative_path_jumps_le_index_indicator_liminf
      Y S T hT ε hε hTimes hL hR hJump
  calc
    ENat.toENNReal S.encard ≤ ENat.toENNReal (Filter.liminf f atTop) :=
      ENat.toENNReal_mono hindex
    _ = Filter.liminf (fun n => ENat.toENNReal (f n)) atTop :=
      avram_p2_34dbea70_enat_to_ennreal_liminf_commutes f
    _ = _ := by
      congr 1
      funext n
      exact avram_p2_34dbea70_enat_to_ennreal_indicator_sum
        (Finset.range (n + 1))
        (fun i => Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2)
