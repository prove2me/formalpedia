-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.deuring_heilbronn_hypergeometric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:01.153372+00:00
-- url     : https://prove2.me/submissions/655d6326-2029-4929-98ee-0065a9189935

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyper
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_diff_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cS_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : DHHyper := by
  refine ⟨400, by norm_num, ?_⟩
  intro M _ χ₁ y x hM _ hne hy hyx
  have e : ∀ N₀ N₁ : ℕ, N₀ ≤ N₁ → ∑ n ∈ Finset.Ioc N₀ N₁, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) =
      (Hyp.cF χ₁ N₁ - Hyp.cF χ₁ N₀).re := by
    intro N₀ N₁ h
    rw [Hyp.cF, Hyp.cF, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N₀) h, add_sub_cancel_left,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.div_natCast_re]
  have h0 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have h01 : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
  rw [e _ _ h01]
  have hd := Hyp.diff_bound χ₁ hne ⌊y⌋₊ ⌊x⌋₊ h0 h01
  set N₀ := ⌊y⌋₊ with hN₀
  set N₁ := ⌊x⌋₊ with hN₁
  set L := DirichletCharacter.LFunction χ₁ 1
  set B := (M : ℝ) + 1 with hBdef
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hN0y : (N₀ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyN0 : y < N₀ + 1 := Nat.lt_floor_add_one y
  have hN1x : (N₁ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy

  have hlog1 : Real.log N₁ ≤ Real.log x := Real.log_le_log (by linarith) hN1x
  have hlog0 : Real.log y - Real.log N₀ ≤ 2 / y := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.log_le_sub_one_of_pos (show 0 < y / N₀ by positivity)
    have h' : y / N₀ - 1 ≤ 2 / y := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith
  have hxy : Real.log (x / y) = Real.log x - Real.log y := Real.log_div (by linarith) (by linarith)

  have hLB : ‖L‖ ≤ 5 * B := by
    have h := Hyp.cS_approx χ₁ hne 1 le_rfl
    have h1 : Hyp.cS χ₁ 1 = 1 := by simp [Hyp.cS]
    rw [h1] at h
    have := norm_sub_norm_le L 1
    simp only [norm_one, Nat.cast_one, div_one] at h this
    linarith

  have hsy : 0 < √y := Real.sqrt_pos.mpr (by linarith)
  have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsyN : √y ≤ 2 * √(N₀ : ℝ) := by
    have h4 : (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) = 4 * N₀ := by
      have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) N₀); nlinarith
    have := Real.sqrt_le_sqrt (show y ≤ (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) by rw [h4]; linarith)
    rwa [Real.sqrt_mul_self (by positivity)] at this
  have hlN0 : Real.log N₀ ≤ Real.log y := Real.log_le_log (by linarith) hN0y
  set Y := (Real.log y + 1) / √y with hY
  have hY0 : 0 ≤ Y := by positivity
  have hg0 : (Real.log N₀ + 1) / √(N₀ : ℝ) ≤ 2 * Y := by
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ hs0 hsy]
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    nlinarith
  have hyY : 2 / y ≤ 2 * Y := by
    have hsyy : √y ≤ y := by
      have := Real.sqrt_le_sqrt (show y ≤ y * y by nlinarith)
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ (by linarith) hsy]
    nlinarith
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have i1 : ‖L‖ * (Real.log N₁ - Real.log N₀) ≤ ‖L‖ * Real.log (x / y) + ‖L‖ * (2 / y) := by
    rw [hxy, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hLn
  have i2 : ‖L‖ * (2 / y) ≤ 5 * B * (2 * Y) := mul_le_mul hLB hyY (by positivity) (by positivity)
  have i3 : 86 * B * ((Real.log N₀ + 1) / √(N₀ : ℝ)) ≤ 86 * B * (2 * Y) :=
    mul_le_mul_of_nonneg_left hg0 (by positivity)
  have e3 : 400 * (M : ℝ) * (Real.log y + 1) / √y = 400 * M * Y := by rw [hY]; ring
  rw [e3]
  have hB2 : B ≤ 2 * M := by rw [hBdef]; linarith
  have i4 : 5 * B * (2 * Y) + 86 * B * (2 * Y) ≤ 400 * M * Y := by nlinarith
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
