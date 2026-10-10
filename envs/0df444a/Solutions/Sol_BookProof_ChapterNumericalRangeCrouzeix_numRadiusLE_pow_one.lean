-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:41.673255+00:00
-- url     : https://prove2.me/submissions/bc4473ce-2ef9-48d3-81e6-8bd69447e8fa

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_re_inner_sub_smul_nonneg
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numRadiusLE_of_re_inner_sub_smul_nonneg
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_pearcyVec_apply
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_sum_pearcyVec
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} (h : NumRadiusLE A 1) (n : ℕ) (hn : 0 < n) :
    NumRadiusLE (A ^ n) 1 := by

  refine numRadiusLE_of_re_inner_sub_smul_nonneg ?_
  intro q hq y
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ n = q := IsAlgClosed.exists_pow_nat_eq q hn
  have hzlt : ‖z‖ < 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (1:ℝ) ≤ ‖z‖ ^ n := one_le_pow₀ hcon
    rw [← norm_pow, hz] at h1
    linarith
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hwdef
  have hw : IsPrimitiveRoot w n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hwnorm : ‖w‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw.pow_eq_one hn.ne'
  set W : E := y - q • (A ^ n) y with hW
  have hsolve : ∀ k : ℕ, pearcyVec A (w ^ k * z) n y
      - (w ^ k * z) • A (pearcyVec A (w ^ k * z) n y) = W := by
    intro k
    rw [pearcyVec_apply, hW]
    congr 2
    rw [mul_pow, ← pow_mul, mul_comm k n, pow_mul, hw.pow_eq_one, one_pow, one_mul, hz]
  have hnorm_c : ∀ k : ℕ, ‖w ^ k * z‖ ≤ 1 := by
    intro k
    rw [norm_mul, norm_pow, hwnorm, one_pow, one_mul]
    exact hzlt.le
  have hterm : ∀ k : ℕ, 0 ≤ (⟪pearcyVec A (w ^ k * z) n y, W⟫_ℂ).re := by
    intro k
    have hk := re_inner_sub_smul_nonneg h (hnorm_c k) (pearcyVec A (w ^ k * z) n y)
    rwa [hsolve k] at hk
  have hsum : ⟪((n : ℂ) • y), W⟫_ℂ
      = ∑ k ∈ Finset.range n, ⟪pearcyVec A (w ^ k * z) n y, W⟫_ℂ := by
    rw [← sum_pearcyVec hn hw z y, sum_inner]
  have hre : 0 ≤ (⟪((n : ℂ) • y), W⟫_ℂ).re := by
    rw [hsum, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => hterm k
  rw [inner_smul_left] at hre
  simp only [map_natCast, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero] at hre
  have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  nlinarith [hre]
