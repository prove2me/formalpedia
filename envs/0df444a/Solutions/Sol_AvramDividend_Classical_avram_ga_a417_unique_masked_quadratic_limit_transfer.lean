-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a417_unique_masked_quadratic_limit_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:40:05.579278+00:00
-- url     : https://prove2.me/submissions/2a52a34e-9a3b-46d7-9c24-d6a1140853a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a394_unique_masked_sum_absolute_dominated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
noncomputable section
set_option maxHeartbeats 800000

theorem solution
    (Mask : ℕ → ℕ → Prop) [∀ m i, Decidable (Mask m i)]
    (Z H : ℕ → ℕ → ℝ) (δ : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hδ : ∀ m, 0 ≤ δ m)
    (hUnique : ∀ m i j, Mask m i → Mask m j → i = j)
    (hCell : ∀ m i, i < m → Mask m i →
      |H m i| ≤ K * (|Z m i| + (Z m i)^2 + δ m))
    (hSource : Tendsto
      (fun m : ℕ => ∑ i ∈ Finset.range m,
        if Mask m i then |Z m i| else 0) atTop (𝓝 (0 : ℝ)))
    (hWidth : Tendsto δ atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m,
      if Mask m i then |H m i| else 0) atTop (𝓝 (0 : ℝ)) := by
  classical
  let S : ℕ → ℝ := fun m => ∑ i ∈ Finset.range m,
    if Mask m i then |Z m i| else 0
  let R : ℕ → ℝ := fun m => ∑ i ∈ Finset.range m,
    if Mask m i then |H m i| else 0
  let B : ℕ → ℝ := fun m => K * (S m + (S m)^2 + δ m)
  have hs (m : ℕ) : 0 ≤ S m := by
    dsimp [S]; exact Finset.sum_nonneg (fun i hi => by split_ifs <;> positivity)
  have hr (m : ℕ) : 0 ≤ R m := by
    dsimp [R]; exact Finset.sum_nonneg (fun i hi => by split_ifs <;> positivity)
  have hb (m : ℕ) : 0 ≤ B m := by
    dsimp [B]
    exact mul_nonneg hK (add_nonneg
      (add_nonneg (hs m) (sq_nonneg _)) (hδ m))
  have hBound (m : ℕ) : R m ≤ B m := by
    have hsum := avram_ga_a394_unique_masked_sum_absolute_dominated
      m (Mask m) (fun i => |H m i|) (B m) (hb m) (hUnique m)
      (by
        intro i hi hmi
        have hzi : |Z m i| ≤ S m := by
          have hp := Finset.single_le_sum
            (s := Finset.range m)
            (f := fun k => if Mask m k then |Z m k| else 0)
            (fun k hk => by split_ifs <;> positivity)
            (Finset.mem_range.mpr hi)
          simpa only [if_pos hmi, S] using hp
        have hzi2 : (Z m i)^2 ≤ (S m)^2 := by
          nlinarith [sq_abs (Z m i),
            mul_nonneg (sub_nonneg.mpr hzi)
              (add_nonneg (hs m) (abs_nonneg (Z m i)))]
        have hvalue := hCell m i hi hmi
        rw [abs_abs]
        exact hvalue.trans (mul_le_mul_of_nonneg_left
          (by nlinarith [hzi, hzi2]) hK))
    simpa only [R, abs_of_nonneg (hr m)] using hsum
  have hS : Tendsto S atTop (𝓝 (0 : ℝ)) := hSource
  have hB : Tendsto B atTop (𝓝 (0 : ℝ)) := by
    have ht := ((hS.add (hS.pow 2)).add hWidth)
    have hc : Tendsto (fun _ : ℕ => K) atTop (𝓝 K) := tendsto_const_nhds
    have h := hc.mul ht
    simpa only [zero_add, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, B] using h
  exact squeeze_zero hr hBound hB
