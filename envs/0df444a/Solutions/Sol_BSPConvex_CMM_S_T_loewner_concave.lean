-- Prove2me | solution 1 for BSPConvex.CMM.S_T_loewner_concave
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:31:14.911257+00:00
-- url     : https://prove2.me/submissions/3b2c3124-6d69-44e1-9b86-751f0e553e2c

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

open BSPConvex.CMM in
theorem solution {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef)
    (x y : Fin m → ℝ) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    Smat (lam • x + (1 - lam) • y) =
        lam • Smat x + (1 - lam) • Smat y + (lam * (1 - lam)) • Matrix.vecMulVec (x - y) (x - y) ∧
      (Smat (lam • x + (1 - lam) • y) - (lam • Smat x + (1 - lam) • Smat y)).PosSemidef ∧
      (Tmat Sig (lam • x + (1 - lam) • y) - (lam • Tmat Sig x + (1 - lam) • Tmat Sig y)).PosSemidef := by
  have h1 : Smat (lam • x + (1 - lam) • y) =
      lam • Smat x + (1 - lam) • Smat y + (lam * (1 - lam)) • Matrix.vecMulVec (x - y) (x - y) := by
    ext i j
    simp only [Smat, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Matrix.diagonal_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    split_ifs <;> ring
  have hdiff : Smat (lam • x + (1 - lam) • y) - (lam • Smat x + (1 - lam) • Smat y) =
      (lam * (1 - lam)) • Matrix.vecMulVec (x - y) (x - y) := by
    rw [h1]; abel
  have h2 : (Smat (lam • x + (1 - lam) • y) - (lam • Smat x + (1 - lam) • Smat y)).PosSemidef := by
    rw [hdiff]
    have := Matrix.posSemidef_vecMulVec_self_star (x - y)
    rw [star_trivial] at this
    exact this.smul (mul_nonneg hlam.1 (by linarith [hlam.2]))
  refine ⟨h1, h2, ?_⟩
  have hT : Tmat Sig (lam • x + (1 - lam) • y) - (lam • Tmat Sig x + (1 - lam) • Tmat Sig y) =
      CFC.sqrt Sig * (Smat (lam • x + (1 - lam) • y) - (lam • Smat x + (1 - lam) • Smat y)) *
        CFC.sqrt Sig := by
    simp only [Tmat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [hT]
  have hs : (CFC.sqrt Sig).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sig)
  have hH : (CFC.sqrt Sig)ᴴ = CFC.sqrt Sig := hs.isHermitian.eq
  have := h2.conjTranspose_mul_mul_same (CFC.sqrt Sig)
  rwa [hH] at this
