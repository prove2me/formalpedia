-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.opNormAt_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:54.224801+00:00
-- url     : https://prove2.me/submissions/38f59bf1-eb74-40bc-a345-bdba32673200

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_dualFrame_inv
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_transpose_isom
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_conjT_transpose_isom
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_basisChange_mul_X
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cU_conj_mul
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cU_mul_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix NumberField Module
noncomputable section
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
section Op
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}
private theorem toMatrix_eq_transpose_mul_mul_of_comp (bN : Basis ιN K VN) (bR : Basis ιR K VR) (eN : (Fin d → K) ≃ₗ[K] VN)
    (eR : (Fin n → K) ≃ₗ[K] VR) (Bk : VN →ₗ[K] Module.Dual K VR)
    (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K)) (hB : ∀ x y, Bk (eN x) (eR y) = B x y) :
    LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B =
      (LinearMap.toMatrix (Pi.basisFun K (Fin n)) bR eR.toLinearMap)ᵀ *
        LinearMap.toMatrix bN bR.dualBasis Bk *
          LinearMap.toMatrix (Pi.basisFun K (Fin d)) bN eN.toLinearMap := by
  ext a b
  simp only [LinearMap.toMatrix_apply, Basis.dualBasis_repr, Matrix.mul_apply, Matrix.transpose_apply,
    LinearEquiv.coe_coe, Finset.sum_mul]
  rw [← hB]
  conv_lhs => rw [← bN.sum_repr (eN (Pi.basisFun K (Fin d) b)), ← bR.sum_repr (eR (Pi.basisFun K (Fin n) a))]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem toMatrix_map_embedding_eq_cP_mul (bN : Basis ιN K VN) (bR : Basis ιR K VR) (eN : (Fin d → K) ≃ₗ[K] VN)
    (eR : (Fin n → K) ≃ₗ[K] VR) (Bk : VN →ₗ[K] Module.Dual K VR)
    (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K)) (hB : ∀ x y, Bk (eN x) (eR y) = B x y)
    (v : InfinitePlace K) :
    (LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B).map v.embedding =
      (cP bR eR v)ᵀ * (LinearMap.toMatrix bN bR.dualBasis Bk).map v.embedding * cP bN eN v := by
  rw [toMatrix_eq_transpose_mul_mul_of_comp bN bR eN eR Bk B hB, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rfl
private theorem opNorm_toEuclideanLin_mul_le {l m o : Type} [Fintype l] [Fintype m] [Fintype o] [DecidableEq l]
    [DecidableEq m] [DecidableEq o] (A : Matrix l m ℂ) (B : Matrix m o ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A * B))‖ ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ *
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)‖ := by
  have h := Matrix.l2_opNorm_mul A B
  simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using h
private theorem opNorm_toEuclideanLin_le_one_of_isometry {l m : Type} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
    (W : Matrix l m ℂ) (hW : Wᴴ * W = 1) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin W)‖ ≤ 1 := by
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self W
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix m m ℂ)
  rw [hW] at h1
  rw [Matrix.conjTranspose_one, Matrix.one_mul] at h2
  simp only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] at h1 h2
  have hs := norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin W))
  have ht := norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix m m ℂ)))
  have ht1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix m m ℂ))‖ ≤ 1 := by
    nlinarith
  nlinarith
private theorem opNorm_toEuclideanLin_unitary_mul_mul_eq {a b c e : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq e]
    (M : Matrix a b ℂ) (L : Matrix c a ℂ) (R : Matrix b e ℂ) (L' : Matrix a c ℂ) (R' : Matrix e b ℂ)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (hL' : L'ᴴ * L' = 1) (hR' : R'ᴴ * R' = 1)
    (hLL : L' * L = 1) (hRR : R * R' = 1) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖ =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ := by
  apply le_antisymm
  · calc _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M))‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ := opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ := by
          gcongr; exact opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (1 * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖) * 1 := by
          gcongr
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hL
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hR
      _ = _ := by ring
  · have hM : M = L' * (L * M * R) * R' := by
      calc M = (L' * L) * M * (R * R') := by rw [hLL, hRR, Matrix.one_mul, Matrix.mul_one]
        _ = L' * (L * M * R) * R' := by simp only [Matrix.mul_assoc]
    conv_lhs => rw [hM]
    calc _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L' * (L * M * R)))‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R')‖ := opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L')‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R')‖ := by
          gcongr; exact opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (1 * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖) * 1 := by
          gcongr
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hL'
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hR'
      _ = _ := by ring
end Op
end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end

set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (bN : Basis ιN K VN) (XN : InfinitePlace K → Matrix ιN ιN ℂ) (bR : Basis ιR K VR)
    (XR : InfinitePlace K → Matrix ιR ιR ℂ) (Xc : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (eN : (Fin d → K) ≃ₗ[K] VN) (eR : (Fin n → K) ≃ₗ[K] VR)
    (hN : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bN XN v (eN x) (eN y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) Xc v x y)
    (hR : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bR XR v (eR x) (eR y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXN : ∀ v, IsUnit (XN v).det) (hXR : ∀ v, IsUnit (XR v).det) (hXc : ∀ v, IsUnit (Xc v).det)
    (hXE : ∀ v, IsUnit (XE v).det)
    (Bk : VN →ₗ[K] Module.Dual K VR) (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K))
    (hB : ∀ x y, Bk (eN x) (eR y) = B x y) (v : InfinitePlace K) :
    Formalism.HN.opNormAt bN XN bR.dualBasis (Formalism.HN.dualFrame XR) v Bk =
      Formalism.HN.opNormAt (Pi.basisFun K (Fin d)) Xc (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) v B := by
  have key : (Formalism.HN.dualFrame XE v)⁻¹ *
        (LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B).map v.embedding *
          Xc v =
      (cU bR XR XE eR v)ᵀ * ((Formalism.HN.dualFrame XR v)⁻¹ *
        (LinearMap.toMatrix bN bR.dualBasis Bk).map v.embedding * XN v) * cU bN XN Xc eN v := by
    have h1 := basisChange_mul_X (b := bR) (e := eR) (X := XE) (XA := XR) (v := v) (hXR v)
    have h2 := basisChange_mul_X (b := bN) (e := eN) (X := Xc) (XA := XN) (v := v) (hXN v)
    rw [dualFrame_inv XE v (hXE v), dualFrame_inv XR v (hXR v), toMatrix_map_embedding_eq_cP_mul bN bR eN eR Bk B hB v]
    simp only [Matrix.mul_assoc]
    rw [h2, ← Matrix.mul_assoc (XE v)ᵀ, ← Matrix.transpose_mul, h1, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  unfold Formalism.HN.opNormAt
  rw [key]
  symm
  refine opNorm_toEuclideanLin_unitary_mul_mul_eq _ _ _ ((cU bR XR XE eR v)ᴴ)ᵀ (cU bN XN Xc eN v)ᴴ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [transpose_isom, cU_mul_conj (h := hR) (hXA := hXR v) (hX := hXE v), Matrix.transpose_one]
  · exact cU_conj_mul (h := hN) (hX := hXc v)
  · rw [conjT_transpose_isom, cU_conj_mul (h := hR) (hX := hXE v), Matrix.transpose_one]
  · rw [Matrix.conjTranspose_conjTranspose]
    exact cU_mul_conj (h := hN) (hXA := hXN v) (hX := hXc v)
  · rw [← Matrix.transpose_mul, cU_mul_conj (h := hR) (hXA := hXR v) (hX := hXE v), Matrix.transpose_one]
  · exact cU_mul_conj (h := hN) (hXA := hXN v) (hX := hXc v)
end Formalism.MainNotions.DIV.HookProducts.RBTie
