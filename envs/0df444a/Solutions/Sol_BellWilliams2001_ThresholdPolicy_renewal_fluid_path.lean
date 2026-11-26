-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.renewal_fluid_path
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:35:47.99067+00:00
-- url     : https://prove2.me/submissions/dd397b43-581d-4aa8-93d1-c570868a7acd

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open Filter Topology BellWilliams2001.ThresholdPolicy

private theorem count_bracket {e : ℕ → ℝ} (he : StrictMono e) (he0 : e 0 = 0)
    (hUnbounded : Tendsto e atTop atTop) {s : ℝ} (hs : 0 ≤ s) :
    ∃ j : ℕ, e j ≤ s ∧ s < e (j + 1) ∧ renewalCount e s = j := by
  have hEx : ∃ i, s < e i := (hUnbounded.eventually_gt_atTop s).exists
  let b := Nat.find hEx
  have hb : s < e b := Nat.find_spec hEx
  have hb0 : b ≠ 0 := by
    intro hh
    rw [hh, he0] at hb
    exact hb.not_ge hs
  let j := b - 1
  have hjb : j + 1 = b := by dsimp [j]; omega
  have hj : e j ≤ s := le_of_not_gt (Nat.find_min hEx (by omega : j < b))
  have hj' : s < e (j + 1) := by rwa [hjb]
  refine ⟨j, hj, hj', le_antisymm ?_ ?_⟩
  · unfold renewalCount
    refine iSup_le fun i => iSup_le fun hi => ?_
    have h : i ≤ j := by
      by_contra! h
      exact (hj'.trans_le (he.monotone h)).not_ge hi
    exact_mod_cast h
  · unfold renewalCount
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

private theorem linear_error {e : ℕ → ℝ}
    (hmean : Tendsto (fun m : ℕ => e m / (m : ℝ)) atTop (𝓝 1))
    {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      |e m - (m : ℝ)| ≤ δ * m + C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hmean δ hδ).and
    (eventually_ge_atTop (1 : ℕ)))
  let C : ℝ := ∑ k ∈ Finset.range N, |e k - (k : ℝ)|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C, hC, fun m => ?_⟩
  by_cases h : N ≤ m
  · obtain ⟨hnear, hm1⟩ := hN m h
    have hm : 0 < (m : ℝ) := by exact_mod_cast hm1
    rw [Real.dist_eq, ← div_self hm.ne', ← sub_div, abs_div, abs_of_pos hm] at hnear
    exact ((div_lt_iff₀ hm).1 hnear).le.trans (le_add_of_nonneg_right hC)
  · have hmem : m ∈ Finset.range N := Finset.mem_range.2 (lt_of_not_ge h)
    exact (Finset.single_le_sum (f := fun k => |e k - (k : ℝ)|)
      (fun _ _ => abs_nonneg _) hmem).trans (le_add_of_nonneg_left (by positivity))

set_option maxHeartbeats 700000 in
theorem solution (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (hUnbounded : Tendsto e atTop atTop)
    (hmean : Tendsto (fun m : ℕ => e m / (m : ℝ)) atTop (𝓝 1))
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (H : ℝ) (hH : 0 ≤ H)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ∈ Set.Icc 0 (R n * H),
      |((renewalCount e s).toNat : ℝ) - s| ≤ ε * R n := by
  let δ := min (1 / 4 : ℝ) (ε / (4 * (H + 1)))
  have hd0 : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 / 4 := min_le_left _ _
  have hdSmall : δ * (4 * (H + 1)) ≤ ε := by
    exact (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  obtain ⟨C, hC, hErr⟩ := linear_error hmean hd0
  filter_upwards [hR.eventually_ge_atTop (max 1 ((8 * (C + 1)) / ε))] with n hn
  have hn1 : 1 ≤ R n := (le_max_left _ _).trans hn
  have hn2 : 8 * (C + 1) ≤ ε * R n := by
    have h := (div_le_iff₀ hε).1 ((le_max_right _ _).trans hn)
    simpa only [mul_comm (R n)] using h
  intro s hs
  obtain ⟨j, hj, hj', hjv⟩ := count_bracket he he0 hUnbounded hs.1
  rw [hjv, ENat.toNat_natCast]
  have hδH : 4 * (δ * H) ≤ ε := by nlinarith [mul_nonneg hd0.le (show 0 ≤ H by exact hH)]
  have hδHR : 4 * (δ * H * R n) ≤ ε * R n := by
    have h := mul_le_mul_of_nonneg_right hδH (show 0 ≤ R n by linarith)
    linarith only [h]
  have hu := (abs_le.1 (hErr j)).1
  have hl := (abs_le.1 (hErr (j + 1))).2
  push_cast at hl
  have hjupper : (j : ℝ) - s ≤ 2 * (δ * s + C) := by
    have hk : (j : ℝ) - s ≤ δ * (j : ℝ) + C := by linarith
    have hh : (1 - δ) * ((j : ℝ) - s) ≤ δ * s + C := by linarith only [hk]
    by_cases h : (j : ℝ) - s ≤ 0
    · exact h.trans (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hd0.le hs.1) hC))
    · have hh' := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1 - δ by linarith)
        (le_of_lt (lt_of_not_ge h))
      linarith only [hh, hh']
  have hjlower : s - (j : ℝ) ≤ δ * s + C + 2 := by
    by_cases h : s ≤ (j : ℝ)
    · linarith [mul_nonneg hd0.le hs.1]
    · have hjS : δ * (j : ℝ) ≤ δ * s := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) hd0.le
      linarith
  have hds : δ * s ≤ δ * H * R n := by
    simpa only [mul_comm (R n) H, ← mul_assoc] using mul_le_mul_of_nonneg_left hs.2 hd0.le
  exact abs_le.2 ⟨by linarith, by linarith⟩
