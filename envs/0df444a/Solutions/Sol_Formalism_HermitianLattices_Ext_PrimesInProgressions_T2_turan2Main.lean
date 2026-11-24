-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.turan2Main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:58.195636+00:00
-- url     : https://prove2.me/submissions/95158de9-4b3f-40c0-8f5d-cddb9454c8f8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsFarFromPoints
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_RootNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_Turan2Main
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_prodLower
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_Tbound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_avgLimit
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_prodDist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (n m : ℕ) (z : Fin n → ℂ) (hn : 1 ≤ n) (hz : ∀ i, ‖z i‖ ≤ 1) (hz1 : ∃ i, ‖z i‖ = 1) :
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + n ∧ ((n : ℝ) / (1600 * ((m : ℝ) + n))) ^ n ≤ ‖∑ i, z i ^ k‖ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hz1
  set B : ℝ := ((n : ℝ) / (1600 * ((m : ℝ) + n))) ^ n with hBdef
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hM : (0 : ℝ) < (m : ℝ) + n := by linarith
  have hnM : (n : ℝ) ≤ (m : ℝ) + n := by linarith
  have hq1 : m + 1 ≤ (m + n) / n * n := by
    have h1 := Nat.div_add_mod (m + n) n
    have h2 := Nat.mod_lt (m + n) (show n > 0 by omega)
    rw [Nat.mul_comm] at h1
    generalize (m + n) / n * n = Q at h1 ⊢
    generalize (m + n) % n = t at h1 h2
    omega
  have hq2 : (((m + n) / n : ℕ) : ℝ) * (n : ℝ) ≤ (m : ℝ) + n := by
    exact_mod_cast Nat.div_mul_le_self (m + n) n
  set q : ℕ := (m + n) / n with hqdef
  set M : ℝ := (m : ℝ) + n with hMdef
  set r : ℝ := (n : ℝ) / (6 * M) with hr
  have hr0 : 0 < r := div_pos (by linarith) (by linarith)
  have hr6 : r ≤ 1 / 6 := by
    rw [hr, div_le_iff₀ (by linarith)]; linarith
  obtain ⟨ρ, hρc, hP⟩ := prodDist (fun i : Fin n => ‖z i‖) Finset.univ (1 - 2 * r) r hr0
  have hP' : (r / 25) ^ n ≤ ∏ j : Fin n, |ρ - ‖z j‖| := by
    have h := hP
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  set P : ℝ := ∏ j : Fin n, |ρ - ‖z j‖| with hPdef
  have hρlo : 1 - 3 * r ≤ ρ := by have := (abs_le.mp hρc).1; linarith
  have hρhi : ρ ≤ 1 - r := by have := (abs_le.mp hρc).2; linarith
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hP0 : 0 < P := lt_of_lt_of_le (pow_pos (div_pos hr0 (by norm_num)) n) hP'
  have hρq : (1 : ℝ) / 2 ≤ ρ ^ q := by
    have hb := one_add_mul_le_pow (a := ρ - 1) (by linarith) q
    have he : 1 + (ρ - 1) = ρ := by ring
    rw [he] at hb
    have h3 : (q : ℝ) * (3 * r) ≤ 1 / 2 := by
      have he2 : (q : ℝ) * (3 * r) = ((q : ℝ) * n) / (2 * M) := by rw [hr]; ring_nf
      rw [he2, div_le_iff₀ (by linarith)]; linarith
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - ρ ≤ 3 * r by linarith) hq0]
  have hρm : (1 / 2 : ℝ) ^ n ≤ ρ ^ (m + 1) := by
    calc (1 / 2 : ℝ) ^ n ≤ (ρ ^ q) ^ n := pow_le_pow_left₀ (by norm_num) hρq n
      _ = ρ ^ (q * n) := (pow_mul ρ q n).symm
      _ ≤ ρ ^ (m + 1) := pow_le_pow_of_le_one hρ0.le hρ1.le hq1
  have hkey : (n : ℝ) * (2 ^ n * B) < ρ ^ (m + 1) * P := by
    have hlow : ((n : ℝ) / (300 * M)) ^ n ≤ ρ ^ (m + 1) * P := by
      calc ((n : ℝ) / (300 * M)) ^ n = (1 / 2 : ℝ) ^ n * (r / 25) ^ n := by
            rw [← mul_pow]; congr 1; rw [hr]; ring_nf
        _ ≤ ρ ^ (m + 1) * P :=
            mul_le_mul hρm hP' (pow_pos (div_pos hr0 (by norm_num)) n).le (pow_pos hρ0 _).le
    have hB : (n : ℝ) * (2 ^ n * B) = n * ((3 / 8 : ℝ) ^ n * ((n : ℝ) / (300 * M)) ^ n) := by
      rw [hBdef, ← mul_pow, ← mul_pow]; congr 2; ring_nf
    have hY : 0 < ((n : ℝ) / (300 * M)) ^ n := pow_pos (div_pos (by linarith) (by linarith)) n
    have hsmall : (n : ℝ) * (3 / 8 : ℝ) ^ n < 1 := by
      have hb := one_add_mul_le_pow (a := (5 / 3 : ℝ)) (by norm_num) n
      have h83 : (1 + 5 / 3 : ℝ) = 8 / 3 := by norm_num
      rw [h83] at hb
      have hone : (3 / 8 : ℝ) ^ n * (8 / 3) ^ n = 1 := by rw [← mul_pow]; norm_num
      have hpos : (0 : ℝ) < (3 / 8) ^ n := pow_pos (by norm_num) n
      nlinarith [mul_le_mul_of_nonneg_left hb hpos.le]
    calc (n : ℝ) * (2 ^ n * B) = n * ((3 / 8 : ℝ) ^ n * ((n : ℝ) / (300 * M)) ^ n) := hB
      _ = (n * (3 / 8 : ℝ) ^ n) * ((n : ℝ) / (300 * M)) ^ n := by ring
      _ < 1 * ((n : ℝ) / (300 * M)) ^ n := mul_lt_mul_of_pos_right hsmall hY
      _ = ((n : ℝ) / (300 * M)) ^ n := one_mul _
      _ ≤ ρ ^ (m + 1) * P := hlow
  set ξ : ℂ := ((ρ⁻¹ : ℝ) : ℂ) with hξdef
  have hξ : ‖ξ‖ = ρ⁻¹ := by
    rw [hξdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0)]
  have hρinv1 : 1 < ρ⁻¹ := by
    have hc : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    nlinarith [inv_pos.mpr hρ0]
  have hzρ : ∀ i, ‖z i‖ * ρ⁻¹ ≠ 1 := by
    intro i h
    have hzi : ‖z i‖ = ρ := by
      have h' : ‖z i‖ * ρ⁻¹ * ρ = 1 * ρ := by rw [h]
      rwa [mul_assoc, inv_mul_cancel₀ hρ0.ne', mul_one, one_mul] at h'
    have hP00 : P = 0 := by
      rw [hPdef]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hzi])
    linarith
  set y : Fin n → ℂ := fun i => z i * ξ with hydef
  have hyn : ∀ i, ‖y i‖ = ‖z i‖ * ρ⁻¹ := fun i => by
    show ‖z i * ξ‖ = _
    rw [norm_mul, hξ]
  have hy : ∀ i, ‖y i‖ ≠ 1 := fun i => by rw [hyn]; exact hzρ i
  have hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ B := fun k h1 h2 => (hcon k h1 h2).le
  have hRP : 0 < ρ ^ (m + 1) * P := mul_pos (pow_pos hρ0 _) hP0
  set K : ℝ := ((n : ℝ) * (2 ^ n * B)) / (ρ ^ (m + 1) * P) with hK
  have hKlt : K < 1 := by rw [hK, div_lt_one hRP]; exact hkey
  have hbound : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ (m + 1) / (1 - y i * ζ)‖ ≤ K := by
    intro ζ hζ
    have hnζ' : ‖ξ * ζ‖ = ρ⁻¹ := by rw [norm_mul, hξ, hζ, mul_one]
    have hsum : ∑ i, (y i * ζ) ^ (m + 1) / (1 - y i * ζ)
        = ∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hyz : y i * ζ = z i * (ξ * ζ) := by
        show z i * ξ * ζ = z i * (ξ * ζ)
        ring
      rw [hyz]
    rw [hsum]
    have hne : ∀ i, 1 - z i * (ξ * ζ) ≠ 0 := by
      intro i h
      have h1 : z i * (ξ * ζ) = 1 := (sub_eq_zero.mp h).symm
      have h2 : ‖z i * (ξ * ζ)‖ = 1 := by rw [h1, norm_one]
      rw [norm_mul, hnζ'] at h2
      exact hzρ i h2
    have hA := prodLower n z ρ hρ0 (ξ * ζ) hnζ'
    have hmain := Tbound n m hn z hz B hβ (ξ * ζ) (by rw [hnζ']; exact hρinv1.le) hne
    rw [hnζ'] at hmain
    have hS0 : 0 ≤ ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ := norm_nonneg _
    have h1 : ρ⁻¹ ^ n * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
        ≤ ρ⁻¹ ^ n * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) := by
      calc ρ⁻¹ ^ n * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
            = (ρ⁻¹ ^ n * P) * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ := by ring
        _ ≤ ‖∏ i, (1 - z i * (ξ * ζ))‖ * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ :=
            mul_le_mul_of_nonneg_right hA hS0
        _ ≤ ρ⁻¹ ^ (m + 1) * (n * (ρ⁻¹ ^ n * (2 ^ n * B))) := hmain
        _ = ρ⁻¹ ^ n * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) := by ring
    have h2 : P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖
        ≤ ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B)) :=
      le_of_mul_le_mul_left h1 (pow_pos (inv_pos.mpr hρ0) n)
    have h3 : ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
        ≤ n * (2 ^ n * B) := by
      calc ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
            ≤ ρ ^ (m + 1) * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) :=
            mul_le_mul_of_nonneg_left h2 (pow_pos hρ0 _).le
        _ = (ρ * ρ⁻¹) ^ (m + 1) * (n * (2 ^ n * B)) := by rw [mul_pow]; ring
        _ = n * (2 ^ n * B) := by rw [mul_inv_cancel₀ hρ0.ne', one_pow, one_mul]
    rw [hK, le_div_iff₀ hRP]
    calc ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ * (ρ ^ (m + 1) * P)
          = ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖) := by ring
      _ ≤ n * (2 ^ n * B) := h3
  have hcard := avgLimit y hy (m + 1) (by omega) K hbound
  have hmem : i0 ∈ Finset.univ.filter (fun i => 1 < ‖y i‖) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hyn, hi0, one_mul]
    exact hρinv1
  have hpos : 0 < (Finset.univ.filter (fun i => 1 < ‖y i‖)).card := Finset.card_pos.mpr ⟨i0, hmem⟩
  have hone : (1 : ℝ) ≤ ((Finset.univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) := by exact_mod_cast hpos
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
