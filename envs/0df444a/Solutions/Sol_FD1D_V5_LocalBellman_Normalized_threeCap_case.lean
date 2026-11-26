-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.threeCap_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:52:48.100793+00:00
-- url     : https://prove2.me/submissions/7b78b970-8431-4d33-b70d-f892412ede72

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_A_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_case
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_feedback_case
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_floor_case
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_equal_case
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    let z := min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ))
    residual s r ρ z ≥ (rateIncrement s ρ z + z ^ 2) / 1000 := by
  dsimp
  by_cases hρ : ρ = 0
  · subst ρ
    have hfloor : 0 ≤ floorCap s r 0 := by
      unfold floorCap
      have hden : 0 < s + 1 := by positivity
      norm_num
      exact div_nonneg (by nlinarith) hden.le
    have hchoice :
        min (feedback s 0) (min (uniform s 0) (floorCap s r 0)) = 0 := by
      simp [feedback, uniform, hfloor]
    rw [hchoice]
    exact equal_case hs hr0 hr1
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρ)
  have hApos := A_pos hs hρ0 hρ1
  by_cases hFU : feedback s ρ ≤ uniform s ρ
  · by_cases hFH : feedback s ρ ≤ floorCap s r ρ
    · have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            feedback s ρ :=
        min_eq_left (le_min hFU hFH)
      rw [hchoice]
      exact feedback_case hs hr0 hr1 hρpos hρ1 hFU
    · have hHF : floorCap s r ρ ≤ feedback s ρ := le_of_not_ge hFH
      have hHU : floorCap s r ρ ≤ uniform s ρ := hHF.trans hFU
      have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            floorCap s r ρ := by
        rw [min_eq_right hHU, min_eq_right hHF]
      rw [hchoice]
      exact floor_case hs hr0 hr1 hρpos hρ1 hHU hHF
  · have hUF : uniform s ρ ≤ feedback s ρ := le_of_not_ge hFU
    by_cases hUH : uniform s ρ ≤ floorCap s r ρ
    · have hA8 : A s ρ ≤ 8 := by
        unfold uniform feedback at hUF
        have hsρ : 0 < s * ρ := mul_pos hs hρpos
        have hmul := (le_div_iff₀ hApos).1 hUF
        nlinarith
      have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            uniform s ρ := by
        rw [min_eq_left hUH, min_eq_right hUF]
      rw [hchoice]
      exact uniform_case hs hr0 hr1 hρ0 hρ1 hA8
    · have hHU : floorCap s r ρ ≤ uniform s ρ := le_of_not_ge hUH
      have hHF : floorCap s r ρ ≤ feedback s ρ := hHU.trans hUF
      have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            floorCap s r ρ := by
        rw [min_eq_right hHU, min_eq_right hHF]
      rw [hchoice]
      exact floor_case hs hr0 hr1 hρpos hρ1 hHU hHF
end FD1D.V5.LocalBellman.Normalized
