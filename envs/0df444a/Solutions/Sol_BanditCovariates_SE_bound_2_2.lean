-- Prove2me | solution 1 for BanditCovariates.SE.bound_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:01:19.703088+00:00
-- url     : https://prove2.me/submissions/741a841f-eacf-4ddc-9afb-2d0bd5e3236b

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

set_option autoImplicit false
open BanditCovariates.SE

theorem solution (T : ℕ) (hT : 1 ≤ T) (γ Δ : ℝ)
    (hγ : 1 ≤ γ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    (stoppingRound T γ Δ : ℝ) ≤
      (19 * γ ^ 2 / Δ ^ 2) * logbar ((T : ℝ) * Δ ^ 2 / (18 * γ ^ 2)) := by
  have hγ0 : 0 < γ := by linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set L : ℝ := logbar ((T : ℝ) * Δ ^ 2 / (18 * γ ^ 2)) with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  set x : ℝ := 19 * γ ^ 2 / Δ ^ 2 * L with hx
  have hΔ2 : Δ ^ 2 ≤ 1 := by nlinarith
  have hΔ2pos : 0 < Δ ^ 2 := by positivity
  have hγ2 : 1 ≤ γ ^ 2 := by nlinarith
  have h19 : 19 ≤ x := by
    have : 19 ≤ 19 * γ ^ 2 / Δ ^ 2 := by
      rw [le_div_iff₀ hΔ2pos]; nlinarith
    rw [hx]; nlinarith
  set τ : ℕ := ⌊x⌋₊ with hτ
  have hτ1 : 1 ≤ τ := Nat.le_floor (by norm_num; linarith)
  have hτx : (τ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hτlow : x - 1 < τ := by
    have := Nat.lt_floor_add_one x
    rw [← hτ] at this
    linarith
  have ht : 18 * x / 19 ≤ (τ : ℝ) := by linarith
  have ht0 : (0 : ℝ) < τ := by exact_mod_cast hτ1
  -- key inequalities
  have hA : 18 * γ ^ 2 * L ≤ Δ ^ 2 * τ := by
    have : Δ ^ 2 * (18 * x / 19) = 18 * γ ^ 2 * L := by
      rw [hx]; field_simp
    nlinarith
  have hB : 18 * γ ^ 2 / Δ ^ 2 ≤ τ := by
    have h1 : 18 * γ ^ 2 / Δ ^ 2 ≤ 18 * x / 19 := by
      rw [hx, div_le_iff₀ hΔ2pos]
      have : 18 * γ ^ 2 ≤ 18 * γ ^ 2 * L := by nlinarith
      have e : 18 * (19 * γ ^ 2 / Δ ^ 2 * L) / 19 * Δ ^ 2 = 18 * γ ^ 2 * L := by field_simp
      rw [e]; exact this
    linarith
  have hlog : logbar ((T : ℝ) / τ) ≤ L := by
    unfold logbar
    apply max_le_max _ le_rfl
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ ht0 (by positivity)]
    rw [div_le_iff₀ hΔ2pos] at hB
    nlinarith
  have hmem : τ ∈ {τ : ℕ | 1 ≤ τ ∧ (3 / 2 : ℝ) * γ * U τ T ≤ Δ} := by
    refine ⟨hτ1, ?_⟩
    unfold U
    have hlb : logbar ((T : ℝ) / τ) ≤ L := hlog
    have hy : 2 * logbar ((T : ℝ) / τ) / τ ≤ Δ ^ 2 / (3 * γ) ^ 2 := by
      rw [div_le_div_iff₀ ht0 (by positivity)]
      nlinarith
    have hs : Real.sqrt (2 * logbar ((T : ℝ) / τ) / τ) ≤ Δ / (3 * γ) := by
      calc Real.sqrt (2 * logbar ((T : ℝ) / τ) / τ) ≤ Real.sqrt (Δ ^ 2 / (3 * γ) ^ 2) :=
            Real.sqrt_le_sqrt hy
        _ = Δ / (3 * γ) := by
            rw [← div_pow, Real.sqrt_sq (by positivity)]
    calc (3 / 2 : ℝ) * γ * (2 * Real.sqrt (2 * logbar ((T : ℝ) / τ) / τ))
        = 3 * γ * Real.sqrt (2 * logbar ((T : ℝ) / τ) / τ) := by ring
      _ ≤ 3 * γ * (Δ / (3 * γ)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Δ := by field_simp
  have hle : stoppingRound T γ Δ ≤ τ := Nat.sInf_le hmem
  calc (stoppingRound T γ Δ : ℝ) ≤ τ := by exact_mod_cast hle
    _ ≤ x := hτx
