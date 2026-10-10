-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:43.270205+00:00
-- url     : https://prove2.me/submissions/73eb5a51-4583-4b85-b735-688ee509c647

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numRadiusLE_pow_one
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) (n : ℕ)
    (hn : 0 < n) : NumRadiusLE (A ^ n) (r ^ n) := by

  rcases eq_or_lt_of_le hr with hr0 | hr0
  · -- `r = 0` forces `A = 0`
    have hA : (A : E →ₗ[ℂ] E) = 0 := by
      refine (inner_map_self_eq_zero (A : E →ₗ[ℂ] E)).mp ?_
      intro x
      have hx := h x
      rw [← hr0] at hx
      simp only [zero_mul, norm_le_zero_iff] at hx
      have : (⟪A x, x⟫_ℂ) = (starRingEnd ℂ) (⟪x, A x⟫_ℂ) := (inner_conj_symm _ _).symm
      simp [this, hx]
    have hA0 : A = 0 := by
      ext x
      have := congrArg (fun (T : E →ₗ[ℂ] E) => T x) hA
      simpa using this
    intro x
    rw [hA0]
    simp [zero_pow hn.ne']
    positivity
  · -- scale to numerical radius `1`
    set B : E →L[ℂ] E := (r : ℂ)⁻¹ • A with hB
    have hB1 : NumRadiusLE B 1 := by
      intro x
      have hx := h x
      rw [hB]
      simp only [ContinuousLinearMap.smul_apply, inner_smul_right, norm_mul, norm_inv]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      rw [inv_mul_le_iff₀ hr0]
      calc ‖(⟪x, A x⟫_ℂ)‖ ≤ r * ‖x‖ ^ 2 := hx
        _ = r * (1 * ‖x‖ ^ 2) := by ring
    have hBn := numRadiusLE_pow_one hB1 n hn
    intro x
    have hBpow : (B ^ n) x = ((r : ℂ)⁻¹) ^ n • (A ^ n) x := by
      rw [hB, smul_pow]
      simp
    have hx := hBn x
    rw [hBpow, inner_smul_right, norm_mul] at hx
    have hrn : ‖(((r : ℂ)⁻¹) ^ n)‖ = (r ^ n)⁻¹ := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, ← inv_pow]
    rw [hrn, one_mul, inv_mul_le_iff₀ (by positivity)] at hx
    calc ‖(⟪x, (A ^ n) x⟫_ℂ)‖ ≤ r ^ n * ‖x‖ ^ 2 := by linarith [hx]
      _ = r ^ n * ‖x‖ ^ 2 := rfl
