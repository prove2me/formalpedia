-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_uniform_centered_grid_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:24:06.412443+00:00
-- url     : https://prove2.me/submissions/8cbbd740-d946-443e-aef1-def0c06d05f8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uniform_physical_grid_prefix_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (T : ℝ) (u v : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0) (hv0 : ∀ n, v n 0 = 0)
    (huWidth : ∀ n i, i < n + 1 →
      (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2))
    (hvWidth : ∀ n i, i < n + 1 →
      (v n (i + 1) : ℝ) - (v n i : ℝ) = T / ((n : ℝ) + 2))
    (M : ℕ → ℝ≥0 → Ω → ℝ)
    (hV : ∀ n,
      Integrable
        (fun ω => Finset.sum (Finset.range (n + 1)) (fun i => M n (v n (i + 1)) ω - M n (v n i) ω)) P ∧
      (∫ ω, (Finset.sum (Finset.range (n + 1)) (fun i => M n (v n (i + 1)) ω - M n (v n i) ω)) ∂P) = 0) :
    ∀ n,
      Integrable
        (fun ω => Finset.sum (Finset.range (n + 1)) (fun i => M n (u n (i + 1)) ω - M n (u n i) ω)) P ∧
      (∫ ω, (Finset.sum (Finset.range (n + 1)) (fun i => M n (u n (i + 1)) ω - M n (u n i) ω)) ∂P) = 0 := by
  have hPrefix :=
    avram_bv_meas7_uniform_physical_grid_prefix_unique
      T u v hu0 hv0 huWidth hvWidth
  intro n
  have hFun :
      (fun ω : Ω => Finset.sum (Finset.range (n + 1)) (fun i => M n (u n (i + 1)) ω - M n (u n i) ω)) =
      (fun ω : Ω => Finset.sum (Finset.range (n + 1)) (fun i => M n (v n (i + 1)) ω - M n (v n i) ω)) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    rw [hPrefix n (i + 1) (Nat.succ_le_of_lt hi'),
      hPrefix n i (Nat.le_of_lt hi')]
  simpa only [hFun] using hV n