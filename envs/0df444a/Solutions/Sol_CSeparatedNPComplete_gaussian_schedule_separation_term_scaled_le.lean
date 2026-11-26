-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_separation_term_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:24.986932+00:00
-- url     : https://prove2.me/submissions/219e1195-401b-4223-922d-5f282fe976fa

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {m : ℝ} {k i j : ℕ}
    (hm : 2 ≤ m) (hki : k < i) (hij : i < j) :
    (m + 1) * (m ^ i - m ^ k) ^ 2 ≤ (m ^ j - m ^ k) ^ 2 := by
  have hm0 : 0 ≤ m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hdi : 0 ≤ m ^ i - m ^ k := sub_nonneg.mpr (pow_le_pow_right₀ hm1 hki.le)
  have hpow : m * m ^ i ≤ m ^ j := by
    simpa only [pow_succ, mul_comm] using pow_le_pow_right₀ hm1 (Nat.succ_le_of_lt hij)
  have hpk : 0 ≤ m ^ k := pow_nonneg hm0 _
  have hscale : m * (m ^ i - m ^ k) ≤ m ^ j - m ^ k := by nlinarith
  have hsquare : (m * (m ^ i - m ^ k)) ^ 2 ≤ (m ^ j - m ^ k) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hm0 hdi) hscale 2
  have hcoeff : m + 1 ≤ m ^ 2 := by nlinarith
  calc
    (m + 1) * (m ^ i - m ^ k) ^ 2 ≤ m ^ 2 * (m ^ i - m ^ k) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    _ = (m * (m ^ i - m ^ k)) ^ 2 := by ring
    _ ≤ (m ^ j - m ^ k) ^ 2 := hsquare
end CSeparatedNPComplete
