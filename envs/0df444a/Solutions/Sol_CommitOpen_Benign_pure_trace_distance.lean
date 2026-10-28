-- Prove2me | solution 1 for CommitOpen.Benign.pure_trace_distance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:55:06.945559+00:00
-- url     : https://prove2.me/submissions/c6c3b72c-6c04-4990-8e63-46335b32b362

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace X5CO

open CommitOpen.Benign Matrix
open scoped MatrixOrder ComplexOrder

theorem cube {R : Type*} [Ring R] [Algebra ℂ R] (A B : R) (k : ℂ) (hA : A * A = A)
    (hB : B * B = B) (h1 : A * B * A = k • A) (h2 : B * A * B = k • B) :
    (A - B) * (A - B) * (A - B) = (1 - k) • (A - B) := by
  have e : (A - B) * (A - B) * (A - B) = A * A * A - A * A * B - A * B * A + A * B * B
      - B * A * A + B * A * B + B * B * A - B * B * B := by noncomm_ring
  rw [e, h1, h2, hA, hA, mul_assoc A B B, hB, mul_assoc B A A, hA, hB]
  rw [sub_smul, one_smul, smul_sub]; abel

theorem pure_eq {ι : Type} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    pureState ψ = vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) := by
  ext a b; simp [pureState, vecMulVec_apply]

theorem traceNorm_zero {ι : Type} [Fintype ι] [DecidableEq ι] :
    WildeQIT.traceNorm (0 : Matrix ι ι ℂ) = 0 := by
  simp [WildeQIT.traceNorm]

theorem pure_td {ι : Type} [Fintype ι] [DecidableEq ι] (φ ψ : EuclideanSpace ℂ ι)
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    traceDistance (pureState φ) (pureState ψ) = Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2) := by
  set x := WithLp.ofLp φ
  set y := WithLp.ofLp ψ
  set s : ℂ := inner ℂ ψ φ
  have hxx : star x ⬝ᵥ x = 1 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φ
    rw [EuclideanSpace.inner_eq_star_dotProduct, hφ] at this
    rw [dotProduct_comm]; simpa using this
  have hyy : star y ⬝ᵥ y = 1 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
    rw [EuclideanSpace.inner_eq_star_dotProduct, hψ] at this
    rw [dotProduct_comm]; simpa using this
  have hyx : star y ⬝ᵥ x = s := by
    simp only [s, EuclideanSpace.inner_eq_star_dotProduct, x, y, dotProduct_comm]
  have hxy : star x ⬝ᵥ y = star s := by
    rw [← hyx, dotProduct_comm, ← Matrix.star_dotProduct_star, star_star, dotProduct_comm]
  set A := vecMulVec x (star x)
  set B := vecMulVec y (star y)
  set k : ℂ := star s * s
  have hA : A * A = A := by simp [A, vecMulVec_mul_vecMulVec, hxx]
  have hB : B * B = B := by simp [B, vecMulVec_mul_vecMulVec, hyy]
  have h1 : A * B * A = k • A := by
    simp only [A, B, vecMulVec_mul_vecMulVec, hxy, hyx, vecMulVec_smul, smul_smul, k,
      Matrix.smul_mul]
  have h2 : B * A * B = k • B := by
    simp only [A, B, vecMulVec_mul_vecMulVec, hxy, hyx, vecMulVec_smul, smul_smul, k,
      Matrix.smul_mul]
    rw [mul_comm]
  set D := A - B
  have hDh : Dᴴ = D := by
    simp [D, A, B, conjTranspose_sub, conjTranspose_vecMulVec]
  have hD3 := cube A B k hA hB h1 h2
  have hk : k = ((‖s‖ ^ 2 : ℝ) : ℂ) := by
    simp only [k]; rw [mul_comm, Complex.star_def, Complex.mul_conj']; push_cast; ring
  set c : ℝ := 1 - ‖s‖ ^ 2
  have hc0 : 0 ≤ c := by
    have := norm_inner_le_norm (𝕜 := ℂ) ψ φ
    rw [hφ, hψ, mul_one] at this
    simp only [c]; nlinarith [norm_nonneg s]
  have h1k : (1 - k) = (c : ℂ) := by rw [hk]; simp [c]
  rw [h1k] at hD3
  have htr : (trace (D * D)).re = 2 * c := by
    simp only [D, sub_mul, mul_sub, trace_sub, A, B, vecMulVec_mul_vecMulVec, trace_vecMulVec,
      hxx, hyy, hxy, hyx, one_smul, vecMulVec_smul, trace_smul, smul_eq_mul]
    rw [dotProduct_comm x (star x), dotProduct_comm y (star x), dotProduct_comm x (star y),
      dotProduct_comm y (star y), hxx, hyy, hxy, hyx]
    have : star s * s = ((‖s‖ ^ 2 : ℝ) : ℂ) := hk
    rw [mul_comm s, this]
    simp [c, ← Complex.ofReal_pow]; ring
  have hDD : D * D * D * D = (c : ℂ) • (D * D) := by
    rw [hD3, Matrix.smul_mul]
  unfold traceDistance WildeQIT.traceNorm
  rw [pure_eq, pure_eq]
  change 1 / 2 * (trace (CFC.sqrt (Dᴴ * D))).re = _
  rw [hDh]
  have hpsd : (D * D).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self D; rwa [hDh] at this
  rcases hc0.eq_or_lt with h0 | hpos
  · have e1 : (D * D)ᴴ * (D * D) = 0 := by
      rw [hpsd.1.eq, ← mul_assoc, hDD, ← h0]; simp
    have e2 : D * D = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp e1
    rw [e2, ← h0]; simp
  · set l := Real.sqrt c
    have hl : 0 < l := Real.sqrt_pos.mpr hpos
    have hll : l * l = c := Real.mul_self_sqrt hc0
    have hsq : CFC.sqrt (D * D) = ((l⁻¹ : ℝ) : ℂ) • (D * D) := by
      refine CFC.sqrt_unique ?_ ?_
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_assoc, hDD, smul_smul]
        rw [show ((l⁻¹ : ℝ) : ℂ) * ((l⁻¹ : ℝ) : ℂ) * (c : ℂ) = 1 by
          rw [← hll]; push_cast; field_simp]
        rw [one_smul]
      · rw [Matrix.nonneg_iff_posSemidef]
        exact hpsd.smul (by exact_mod_cast (inv_pos.mpr hl).le)
    rw [hsq, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, htr]
    rw [← hll]; field_simp

end X5CO

open CommitOpen.Benign in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (φ ψ : EuclideanSpace ℂ ι)
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    traceDistance (pureState φ) (pureState ψ) = Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2) :=
  X5CO.pure_td φ ψ hφ hψ
