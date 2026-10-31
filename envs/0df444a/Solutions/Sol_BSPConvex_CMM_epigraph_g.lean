-- Prove2me | solution 1 for BSPConvex.CMM.epigraph_g
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:51:04.551055+00:00
-- url     : https://prove2.me/submissions/18e5ba30-a24c-4078-b992-5d43d80578a4

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model
import Theorems.Thm_BSPConvex_CMM_g_identity

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


theorem h_eq {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) :
    q ⬝ᵥ (Mmat Sig q *ᵥ q) =
      (CFC.sqrt Sig *ᵥ q) ⬝ᵥ ((CFC.sqrt (Tmat Sig q))⁻¹ *ᵥ (CFC.sqrt Sig *ᵥ q)) := by
  have hst : (CFC.sqrt Sig)ᵀ = CFC.sqrt Sig := by
    have := (sqrtSig_psd Sig).isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [Mmat, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hst]

theorem unit_psd_iff (M : Matrix Unit Unit ℝ) : M.PosSemidef ↔ 0 ≤ M () () := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, h⟩
    have := h (fun _ => 1)
    simpa [dotProduct, mulVec] using this
  · intro h
    refine ⟨?_, fun x => ?_⟩
    · ext i j; cases i; cases j; rfl
    · simp only [star_trivial, dotProduct, mulVec, Finset.univ_unique, Finset.sum_singleton]
      have : x () * (M () () * x ()) = M () () * (x () * x ()) := by ring
      rw [this]
      exact mul_nonneg h (mul_self_nonneg _)

/-- A block-diagonal matrix with PSD diagonal blocks is PSD. -/
theorem blockDiag_psd {m : ℕ} (P : Matrix Unit Unit ℝ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · exact IsHermitian.fromBlocks hP.1 (by simp) hQ.1
  · rw [← Sum.elim_comp_inl_inr x, fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add, star_trivial, sumElim_dotProduct_sumElim]
    have h1 := hP.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hQ.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    rw [star_trivial] at h1 h2
    exact add_nonneg h1 h2

theorem bord_add {m : ℕ} (a a' : ℝ) (u v : Fin m → ℝ) (C C' : Matrix (Fin m) (Fin m) ℝ) :
    bord (a + a') u v (C + C') = bord a u v C + fromBlocks (of fun (_ _ : Unit) => a') 0 0 C' := by
  simp only [bord, fromBlocks_add, add_zero]
  congr 1

theorem bord_schur {m : ℕ} (a : ℝ) (v : Fin m → ℝ) (D : Matrix (Fin m) (Fin m) ℝ) (hD : D.PosDef) :
    (bord a v v D).PosSemidef ↔ 0 ≤ a - v ⬝ᵥ (D⁻¹ *ᵥ v) := by
  let _ : Invertible D := hD.isUnit.invertible
  have hB : (of fun (_ : Unit) j => v j)ᴴ = of fun i (_ : Unit) => v i := by
    ext i j; simp
  unfold bord
  rw [← hB, Matrix.PosDef.fromBlocks₂₂ _ _ hD, unit_psd_iff]
  simp only [Matrix.sub_apply, of_apply, Matrix.mul_apply, conjTranspose_apply, star_trivial,
    dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

end BSPCMMAuxG

open BSPConvex.CMM in
theorem solution {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) (t : ℝ) :
    (gFun Sig q ≤ (1 / 2 : ℝ) * t ↔
        t + Matrix.trace (CFC.sqrt (Tmat Sig q)) - q ⬝ᵥ (Mmat Sig q *ᵥ q) ≥ 0) ∧
      (t + Matrix.trace (CFC.sqrt (Tmat Sig q)) - q ⬝ᵥ (Mmat Sig q *ᵥ q) ≥ 0 ↔
        (bord (t + Matrix.trace (CFC.sqrt (Tmat Sig q))) (q ᵥ* CFC.sqrt Sig) (CFC.sqrt Sig *ᵥ q)
          (CFC.sqrt (Tmat Sig q))).PosSemidef) ∧
      ((bord (t + Matrix.trace (CFC.sqrt (Tmat Sig q))) (q ᵥ* CFC.sqrt Sig) (CFC.sqrt Sig *ᵥ q)
          (CFC.sqrt (Tmat Sig q))).PosSemidef ↔
        ∃ (z : ℝ) (Z : Matrix (Fin m) (Fin m) ℝ),
          (bord z (q ᵥ* CFC.sqrt Sig) (CFC.sqrt Sig *ᵥ q) Z).PosSemidef ∧
            t + Matrix.trace (CFC.sqrt (Tmat Sig q)) ≥ z ∧
            (CFC.sqrt (Tmat Sig q) - Z).PosSemidef) := by
  have hg := (g_identity Sig hSig q hq).2
  have hst : (CFC.sqrt Sig)ᵀ = CFC.sqrt Sig := by
    have := (BSPCMMAuxG.sqrtSig_psd Sig).isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have huv : q ᵥ* CFC.sqrt Sig = CFC.sqrt Sig *ᵥ q := by
    rw [← mulVec_transpose, hst]
  rw [huv]
  have hX := BSPCMMAuxG.sqrtT_posDef Sig hSig q hq
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]; constructor <;> intro h <;> linarith
  · rw [BSPCMMAuxG.bord_schur _ _ _ hX, ← BSPCMMAuxG.h_eq]
  · constructor
    · intro h
      exact ⟨_, _, h, le_refl _, by simpa using Matrix.PosSemidef.zero⟩
    · rintro ⟨z, Z, h1, h2, h3⟩
      have e : bord (t + Matrix.trace (CFC.sqrt (Tmat Sig q))) (CFC.sqrt Sig *ᵥ q)
          (CFC.sqrt Sig *ᵥ q) (CFC.sqrt (Tmat Sig q)) =
          bord (z + (t + Matrix.trace (CFC.sqrt (Tmat Sig q)) - z)) (CFC.sqrt Sig *ᵥ q)
          (CFC.sqrt Sig *ᵥ q) (Z + (CFC.sqrt (Tmat Sig q) - Z)) := by
        congr 1 <;> abel
      rw [e, BSPCMMAuxG.bord_add]
      refine h1.add (BSPCMMAuxG.blockDiag_psd _ _ ?_ h3)
      rw [BSPCMMAuxG.unit_psd_iff]
      simp only [of_apply]
      linarith
