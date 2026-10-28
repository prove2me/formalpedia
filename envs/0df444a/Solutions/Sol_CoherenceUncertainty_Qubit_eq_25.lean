-- Prove2me | solution 1 for CoherenceUncertainty.Qubit.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:28:16.21742+00:00
-- url     : https://prove2.me/submissions/0fc41b06-56b0-4a7f-8f1e-4fba0a2b4417

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

open CoherenceUncertainty.Qubit in
theorem solution (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc0 : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    |Real.sqrt (1 - c) - 1 / 2| ≤ |Real.sqrt c - 1 / 2| ∧
      fp p (Real.sqrt c) ≤ fp p (Real.sqrt (1 - c)) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt c := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (1 - c) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = c := by rw [hs, Real.sq_sqrt (by linarith)]
  have hr2 : r ^ 2 = 1 - c := by rw [hr, Real.sq_sqrt (by linarith)]
  have hs1 : s ≤ 1 := by nlinarith
  have hr1 : r ≤ 1 := by nlinarith
  have hshalf : 1 / 2 < s := by nlinarith
  have hrs : r ≤ s := by rw [hr, hs]; exact Real.sqrt_le_sqrt (by linarith)
  have part1 : |r - 1 / 2| ≤ |s - 1 / 2| := by
    rw [abs_of_pos (by linarith : (0:ℝ) < s - 1 / 2)]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hr0 hs0]
    · linarith
  rw [← hs, ← hr]
  refine ⟨part1, ?_⟩
  have hconv : ∀ y, WildeQIT.binaryEntropy y = Real.binEntropy y / Real.log 2 := by
    intro y
    unfold WildeQIT.binaryEntropy Real.binEntropy Real.logb
    rw [Real.log_inv, Real.log_inv]
    ring
  have hsym : ∀ y, Real.binEntropy y = Real.binEntropy (1 / 2 - |y - 1 / 2|) := by
    intro y
    rcases le_total y (1 / 2) with h | h
    · rw [abs_of_nonpos (by linarith)]
      congr 1; ring
    · rw [abs_of_nonneg (by linarith), ← Real.binEntropy_one_sub y]
      congr 1; ring
  have hmono : ∀ y1 y2 : ℝ, 0 ≤ y1 → y1 ≤ 1 → 0 ≤ y2 → y2 ≤ 1 →
      |y1 - 1 / 2| ≤ |y2 - 1 / 2| → Real.binEntropy y2 ≤ Real.binEntropy y1 := by
    intro y1 y2 h1 h1' h2 h2' hd
    rw [hsym y1, hsym y2]
    have hd2 : |y2 - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have hd1 : 0 ≤ |y1 - 1 / 2| := abs_nonneg _
    apply Real.binEntropy_strictMonoOn.monotoneOn
    · constructor <;> norm_num <;> linarith [abs_nonneg (y2 - 1 / 2)]
    · constructor <;> norm_num <;> linarith
    · linarith
  have harg : ∀ x, x * p + (1 - x) * (1 - p) - 1 / 2 = (x - 1 / 2) * (2 * p - 1) := by
    intro x; ring
  have hbd : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ x * p + (1 - x) * (1 - p) ∧
      x * p + (1 - x) * (1 - p) ≤ 1 := by
    intro x hx0 hx1
    constructor <;> nlinarith [mul_nonneg hx0 hp0, mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hp1)]
  unfold fp
  rw [hconv, hconv]
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  apply hmono _ _ (hbd r hr0 hr1).1 (hbd r hr0 hr1).2 (hbd s hs0 hs1).1 (hbd s hs0 hs1).2
  rw [harg, harg, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right part1 (abs_nonneg _)
