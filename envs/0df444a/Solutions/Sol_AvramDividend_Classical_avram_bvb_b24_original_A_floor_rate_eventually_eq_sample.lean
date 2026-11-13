-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b24_original_A_floor_rate_eventually_eq_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:58:25.2379+00:00
-- url     : https://prove2.me/submissions/9adb10c7-2d11-434e-90c7-7c577d5a9095

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_grid_floor_equals_real_sample
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (C τ : ℝ≥0∞)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
       (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (U : ℝ≥0 → ℝ) (ψ : ℝ → ℝ) (q : ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
    ∀ᶠ n : ℕ in atTop,
      (if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
       then
         let s : ℝ≥0 := u n ⌊(t / T) * ((n : ℝ) + 2)⌋₊
         if (s : ℝ≥0∞) < τ ∧ 0 ≤ U s ∧ ENNReal.ofReal (U s) ≤ C
         then Real.exp (-(q * (s : ℝ))) * ψ (U s)
         else 0
       else 0) =
      (let s : ℝ≥0 := Real.toNNReal
        (T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2))
       if (s : ℝ≥0∞) < τ ∧ 0 ≤ U s ∧ ENNReal.ofReal (U s) ≤ C
       then Real.exp (-(q * (s : ℝ))) * ψ (U s)
       else 0) := by
  have hδ : 0 < T - t := sub_pos.mpr htT
  obtain ⟨N, hN⟩ := exists_nat_gt (T / (T - t))
  have hTN : T < (T - t) * (N : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hcut : t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    have hpos : 0 ≤ (T - t) * ((n : ℝ) - (N : ℝ)) :=
      mul_nonneg hδ.le (sub_nonneg.mpr hcast)
    apply (lt_div_iff₀ hden).2
    nlinarith
  have hu :
      u n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ =
      Real.toNNReal
        (T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2)) := by
    apply Subtype.ext
    change (u n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) =
      (Real.toNNReal (T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
        ((n : ℝ) + 2)) : ℝ)
    rw [huniform, Real.coe_toNNReal _ (by positivity)]
  simp [ht0, hcut, hu]
