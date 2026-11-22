-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.mass_corollary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:05.827804+00:00
-- url     : https://prove2.me/submissions/4e4a788f-a2ac-45f5-82e8-9468772ad6c0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OneAddInvPowLeExpOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma one_add_inv_pow_le_exp_one (N : ℕ) (hN : 1 ≤ N) :
    (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc (1 + 1 / (N : ℝ)) ^ N ≤ (Real.exp (1 / N)) ^ N := by
        gcongr
        linarith [Real.add_one_le_exp (1 / (N : ℝ))]
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hN']
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : PowerProductTwoSidedBounds := by
  intro f k T X Γ Dstar dstar dM lo hi hf hk hfk2 hT hX hΓ hD hd hXD hlow hup hdM hlo hhi
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hN : (0:ℝ) < f * k := mul_pos hf' hk'
  have hN1 : 1 ≤ f * k := by simpa using Nat.mul_le_mul hf hk
  have hΓ0 : 0 < Γ := by linarith
  have hT0 : 0 < T := by linarith
  set r : ℝ := -(2:ℝ) / ((f:ℝ) * k) with hr
  set Y : ℝ := X * Γ ^ r with hY
  have hYpos : 0 < Y := mul_pos hX (Real.rpow_pos_of_pos hΓ0 r)
  have hrN : r * ((f * k : ℕ) : ℝ) = -2 := by rw [hr, Nat.cast_mul, div_mul_cancel₀ _ hN.ne']
  have hYN : Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 / dstar := by
    rw [hY, mul_pow, hXD, ← Real.rpow_natCast (Γ ^ r), ← Real.rpow_mul hΓ0.le, hrN, Real.rpow_neg hΓ0.le,
      Real.rpow_two, inv_pow]
    ring
  have hdY : dstar * Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 := by rw [hYN]; field_simp
  have hTk : 1 ≤ T ^ k := one_le_pow₀ (by linarith)
  have hTkpos : 0 < T ^ k := lt_of_lt_of_le one_pos hTk
  have hB : (T ^ k - 1) ^ f ≤ Y ^ (f * k) * Real.exp 1 := by
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := by gcongr <;> linarith
      _ = T ^ (f * k) := by rw [← pow_mul, mul_comm]
      _ ≤ (Y * (1 + 1 / ((f:ℝ) * k))) ^ (f * k) := by gcongr <;> linarith
      _ = Y ^ (f * k) * (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := by rw [mul_pow, Nat.cast_mul]
      _ ≤ Y ^ (f * k) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (one_add_inv_pow_le_exp_one _ hN1) (pow_nonneg hYpos.le _)
  have hq : (f:ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
    have h2k : (2:ℝ) ^ k ≤ T ^ k := by gcongr
    have h2f : (2 * f : ℝ) ≤ 2 ^ k := by exact_mod_cast hfk2
    rw [mul_one_div, div_le_iff₀ hTkpos]
    linarith
  have hle1 : 1 / T ^ k ≤ 1 := (div_le_one hTkpos).2 hTk
  have hBer : 1 + (f:ℝ) * (-(1 / T ^ k)) ≤ (1 + -(1 / T ^ k)) ^ f := one_add_mul_le_pow (by linarith) f
  have hfac : T ^ k - 1 = T ^ k * (1 + -(1 / T ^ k)) := by
    rw [mul_add, mul_one, mul_neg, mul_one_div_cancel hTkpos.ne']
    ring
  have hA : Y ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f := by
    have h1 : Y ^ (f * k) ≤ (T ^ k) ^ f := by
      rw [← pow_mul, mul_comm k f]
      exact pow_le_pow_left₀ hYpos.le hlow _
    have h2 : 1 / 2 ≤ (1 + -(1 / T ^ k)) ^ f := by linarith
    have h3 : 0 ≤ (T ^ k) ^ f := pow_nonneg hTkpos.le _
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    calc Y ^ (f * k) / 2 = Y ^ (f * k) * (1 / 2) := by ring
      _ ≤ (T ^ k) ^ f * (1 / 2) := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ (T ^ k) ^ f * (1 + -(1 / T ^ k)) ^ f := h4
      _ = (T ^ k - 1) ^ f := by rw [hfac, mul_pow]
  have hΓr : Γ ^ r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΓ (by
    rw [hr]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hN.le)
  have hYX : Y ≤ X := mul_le_of_le_one_right hX.le hΓr
  have hinv : 1 / ((f:ℝ) * k) ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hN1)
  have hT2X : T ≤ 2 * X := by nlinarith
  have hlogY : Real.log Y = Real.log X + r * Real.log Γ := by
    rw [hY, Real.log_mul hX.ne' (Real.rpow_pos_of_pos hΓ0 r).ne', Real.log_rpow hΓ0]
  have hr2 : r * Real.log Γ = -(2 * Real.log Γ / ((f:ℝ) * k)) := by rw [hr]; ring
  have hYT : Real.log Y ≤ Real.log T := Real.log_le_log hYpos hlow
  have hT2 : Real.log T ≤ Real.log 2 + Real.log X := by
    rw [← Real.log_mul two_ne_zero hX.ne']
    exact Real.log_le_log hT0 hT2X
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdM, ← hdY]
    calc dstar * Y ^ (f * k) / 2 = dstar * (Y ^ (f * k) / 2) := by ring
      _ ≤ dstar * (T ^ k - 1) ^ f := mul_le_mul_of_nonneg_left hA hd.le
  · rw [hdM, ← hdY]
    calc dstar * (T ^ k - 1) ^ f ≤ dstar * (Y ^ (f * k) * Real.exp 1) := mul_le_mul_of_nonneg_left hB hd.le
      _ = Real.exp 1 * (dstar * Y ^ (f * k)) := by ring
  · linarith
  · linarith
end Formalism.HermitianLattices.GenusMassVolumes
