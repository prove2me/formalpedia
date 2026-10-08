-- Prove2me | solution 1 for GVRPricing.StoppingTime.eq28_shrunk_horizon
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:27:08.631041+00:00
-- url     : https://prove2.me/submissions/5cddf149-2f5d-42fe-906f-658a9b3b9d0e

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_STHeuristic

set_option autoImplicit false

open GVRPricing.StoppingTime in
theorem solution {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    t - (M.lamN k - M.lamN (k + 1)) / (M.lamN k * M.lamN (k + 1)) < shrunkHorizon M k n t ∧
      shrunkHorizon M k n t ≤ t := by
  have hk0 : k < K := by omega
  have ha_eq : M.lamN k = M.lam ⟨k, hk0⟩ := by simp [Menu.lamN, hk0]
  have hb_eq : M.lamN (k + 1) = M.lam ⟨k + 1, hk⟩ := by simp [Menu.lamN, hk]
  have ha : 0 < M.lamN k := by rw [ha_eq]; exact M.lam_pos _
  have hb : 0 < M.lamN (k + 1) := by rw [hb_eq]; exact M.lam_pos _
  have hab : M.lamN (k + 1) < M.lamN k := by
    rw [ha_eq, hb_eq]; apply M.lam_strictAnti; simp [Fin.lt_def]
  set a := M.lamN k with ha_def
  set b := M.lamN (k + 1) with hb_def
  have hamb : 0 < a - b := by linarith
  set x : ℝ := a * tK M k n t with hx_def
  have hx : x = a * ((n : ℝ) - b * t) / (a - b) := by
    rw [hx_def]; unfold tK; rw [← ha_def, ← hb_def]; ring
  have hx0 : 0 ≤ x := by rw [hx]; apply div_nonneg _ hamb.le; apply mul_nonneg ha.le; linarith
  have hm : stM M k n t = ⌈x⌉₊ := rfl
  have hm1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hm2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have key : shrunkHorizon M k n t = t - ((⌈x⌉₊ : ℝ) - x) * (a - b) / (a * b) := by
    unfold shrunkHorizon tm
    rw [hm, ← ha_def, ← hb_def]
    set m : ℝ := (⌈x⌉₊ : ℝ)
    rw [hx]
    field_simp
    ring
  rw [key]
  have hab2 : 0 < a * b := mul_pos ha hb
  constructor
  · have : ((⌈x⌉₊ : ℝ) - x) * (a - b) / (a * b) < (a - b) / (a * b) := by
      apply div_lt_div_of_pos_right _ hab2
      nlinarith
    linarith
  · have : 0 ≤ ((⌈x⌉₊ : ℝ) - x) * (a - b) / (a * b) := by
      apply div_nonneg _ hab2.le
      apply mul_nonneg (by linarith) hamb.le
    linarith
