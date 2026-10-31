-- Prove2me | solution 1 for BSPConvex.CMM.g_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:46:28.148982+00:00
-- url     : https://prove2.me/submissions/2a8c122d-44e2-4f99-9d87-318a8730cc96

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPCMMAuxG
open BSPConvex.CMM

/-- `S(q)` is positive definite on the open simplex. -/
theorem S_posDef {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ intSimplex m) : (Smat x).PosDef := by
  obtain ⟨hx0, hx1⟩ := hx
  have hH : (Smat x).IsHermitian := by
    ext i j
    simp only [Smat, conjTranspose_apply, Matrix.sub_apply, diagonal_apply, vecMulVec_apply,
      star_trivial]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      ring
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro v hv
  set S := ∑ j, x j * v j with hS
  have e1 : ∀ i, (Smat x *ᵥ v) i = x i * v i - x i * S := by
    intro i
    rw [Smat, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
    congr 1
    simp only [mulVec, dotProduct, vecMulVec_apply]
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e2 : ∀ i, v i * (x i * v i - x i * S) = x i * v i ^ 2 - (x i * v i) * S := by
    intro i; ring
  have key : star v ⬝ᵥ (Smat x *ᵥ v) = ∑ i, x i * v i ^ 2 - S ^ 2 := by
    rw [star_trivial]
    simp only [dotProduct, e1]
    rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_sub_distrib, ← Finset.sum_mul, ← hS,
      sq]
  rw [key]
  have hcs : S ^ 2 ≤ (∑ i, x i) * ∑ i, x i * v i ^ 2 := by
    rw [hS]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; exact (hx0 i).le
    · intro i _; exact mul_nonneg (hx0 i).le (sq_nonneg _)
    · intro i _; apply le_of_eq; ring
  have hq : 0 < ∑ i, x i * v i ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    calc (0 : ℝ) < x k * v k ^ 2 := mul_pos (hx0 k) (by positivity)
      _ ≤ ∑ i, x i * v i ^ 2 :=
        Finset.single_le_sum (f := fun i => x i * v i ^ 2)
          (fun i _ => mul_nonneg (hx0 i).le (sq_nonneg _)) (Finset.mem_univ k)
  have : (∑ i, x i) * ∑ i, x i * v i ^ 2 < ∑ i, x i * v i ^ 2 := by
    calc (∑ i, x i) * ∑ i, x i * v i ^ 2 < 1 * ∑ i, x i * v i ^ 2 :=
          mul_lt_mul_of_pos_right hx1 hq
      _ = ∑ i, x i * v i ^ 2 := one_mul _
  linarith

theorem sqrtSig_psd {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) :
    (CFC.sqrt Sig).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sig)

theorem sqrtSig_unit {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef) :
    IsUnit (CFC.sqrt Sig) :=
  (CFC.isUnit_sqrt_iff Sig hSig.posSemidef.nonneg).2 hSig.isUnit

theorem T_posDef {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) : (Tmat Sig q).PosDef := by
  have hs := sqrtSig_psd Sig
  have hH : (CFC.sqrt Sig)ᴴ = CFC.sqrt Sig := hs.isHermitian.eq
  have hpsd := (S_posDef q hq).posSemidef.conjTranspose_mul_mul_same (CFC.sqrt Sig)
  rw [hH] at hpsd
  change (CFC.sqrt Sig * Smat q * CFC.sqrt Sig).PosDef
  rw [hpsd.posDef_iff_isUnit]
  exact ((sqrtSig_unit Sig hSig).mul (S_posDef q hq).isUnit).mul (sqrtSig_unit Sig hSig)

theorem sqrtT_posDef {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) : (CFC.sqrt (Tmat Sig q)).PosDef := by
  have hT := T_posDef Sig hSig q hq
  have hpsd : (CFC.sqrt (Tmat Sig q)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)
  rw [hpsd.posDef_iff_isUnit]
  exact (CFC.isUnit_sqrt_iff _ hT.posSemidef.nonneg).2 hT.isUnit

/-- `tr(S(q) M) = qᵀ diag M − qᵀ M q` for any matrix `M`. -/
theorem trace_S_mul {m : ℕ} (q : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (Smat q * M) = q ⬝ᵥ Matrix.diag M - q ⬝ᵥ (M *ᵥ q) := by
  rw [Matrix.trace_mul_comm, Smat, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  · simp [Matrix.trace, Matrix.mul_diagonal, dotProduct, mul_comm]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct,
      mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring

theorem trace_SM {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) :
    Matrix.trace (Smat q * Mmat Sig q) = Matrix.trace (CFC.sqrt (Tmat Sig q)) := by
  set s := CFC.sqrt Sig
  set r := CFC.sqrt (Tmat Sig q)
  have hr : IsUnit r.det := (Matrix.isUnit_iff_isUnit_det r).1 (sqrtT_posDef Sig hSig q hq).isUnit
  have hrr : r * r = Tmat Sig q := CFC.sqrt_mul_sqrt_self _ (T_posDef Sig hSig q hq).posSemidef.nonneg
  have h1 : Smat q * Mmat Sig q = (Smat q * s * r⁻¹) * s := by
    simp only [Mmat, s, r, Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : s * (Smat q * s * r⁻¹) = r * (r * r⁻¹) := by
    rw [← Matrix.mul_assoc r r, hrr]
    simp only [Tmat, s, Matrix.mul_assoc]
  rw [h2, Matrix.mul_nonsing_inv _ hr, Matrix.mul_one]

end BSPCMMAuxG

open BSPConvex.CMM in
theorem solution {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) :
    gFun Sig q = -(1 / 2 : ℝ) * (q ⬝ᵥ Matrix.diag (Mmat Sig q)) + q ⬝ᵥ (Mmat Sig q *ᵥ q) ∧
      gFun Sig q = -(1 / 2 : ℝ) * Matrix.trace (CFC.sqrt (Tmat Sig q)) +
        (1 / 2 : ℝ) * (q ⬝ᵥ (Mmat Sig q *ᵥ q)) := by
  have h1 : gFun Sig q = -(1 / 2 : ℝ) * (q ⬝ᵥ Matrix.diag (Mmat Sig q)) +
      q ⬝ᵥ (Mmat Sig q *ᵥ q) := by
    simp only [gFun, gradF, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  refine ⟨h1, ?_⟩
  have h2 := BSPCMMAuxG.trace_SM Sig hSig q hq
  rw [BSPCMMAuxG.trace_S_mul] at h2
  rw [h1, ← h2]
  ring
