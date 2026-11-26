-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_4_16
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:58:11.180578+00:00
-- url     : https://prove2.me/submissions/fb57d9df-b671-4043-87e9-8becb8206c97

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace GEPPGrowth.Main.Prop416

open GEPPGrowth.Main

/-- With `P = Q (I - (r - eᵢ) eᵢᵀ)` (`Q` the permutation matrix of `swap 0 i`), the rows `1..d` of `P`
are the compression `D E`, `P r = e₀` and `det P = ±1`. So `updateAt S y i` is the `(0,0)` minor of
`M = P S Pᵀ`, i.e. `adj M 0 0 = det M · (M⁻¹)₀₀ = det S · rᵀ S⁻¹ r`. -/
private lemma key {d : ℕ} (S : Mat (d+1)) (hS : IsUnit S.det) (y : Vec (d+1)) (i : Fin (d+1))
    (hyi : y i ≠ 0) :
    (updateAt S y i).det = S.det * (ratiosAt y i ⬝ᵥ (S⁻¹ *ᵥ ratiosAt y i)) := by
  set r := ratiosAt y i with hr
  set e := basisVector i with he
  set Q : Mat (d+1) := (Equiv.swap 0 i).permMatrix ℝ with hQ
  set F : Mat (d+1) := 1 - Matrix.vecMulVec (r - e) e with hF
  set P := Q * F with hP
  have hri : r i = 1 := by simp [r, ratiosAt, hyi]
  have hPsub : P.submatrix Fin.succ id = compressionAt y i := by
    ext a b
    simp [P, Q, F, compressionAt, deletion, eliminationAt, Matrix.mul_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.vecMulVec_apply]
    have hne : Equiv.swap 0 i a.succ ≠ i := by
      intro h
      exact Fin.succ_ne_zero a ((Equiv.swap 0 i).injective (h.trans (Equiv.swap_apply_left 0 i).symm))
    simp [e, basisVector, hne, r]
  have hPr : P *ᵥ r = Pi.single 0 1 := by
    have hFr : F *ᵥ r = e := by
      funext j
      simp [F, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, e, basisVector]
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Matrix.one_apply, one_mul, hri, Finset.sum_ite_eq]
      ring
    rw [hP, ← Matrix.mulVec_mulVec, hFr]
    funext j
    simp [Q, e, basisVector, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.mulVec, dotProduct]
    simp [Equiv.swap_apply_eq_iff, Pi.single_apply]
  have hdetF : F.det = 1 := by
    rw [hF, Matrix.vecMulVec_eq Unit, Matrix.det_one_sub_mul_comm, Matrix.det_unique]
    simp [Matrix.mul_apply, e, basisVector, hri]
  have hdetP : P.det ^ 2 = 1 := by
    rw [hP, Matrix.det_mul, hdetF, hQ, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (d+1)) i)) with h | h <;>
      simp [h]
  set M := P * S * Pᵀ with hM
  have hMdet : M.det = S.det := by
    simp only [M, Matrix.det_mul, Matrix.det_transpose]
    linear_combination S.det * hdetP
  have hMsub : M.submatrix Fin.succ Fin.succ = updateAt S y i := by
    rw [updateAt, ← hPsub]
    rfl
  have hadj : M.adjugate 0 0 = (updateAt S y i).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp [Fin.succAbove_zero, hMsub]
  have hPu : IsUnit P.det := by
    refine isUnit_iff_ne_zero.2 fun h => ?_
    rw [h] at hdetP; norm_num at hdetP
  have hMinv : M⁻¹ 0 0 = r ⬝ᵥ (S⁻¹ *ᵥ r) := by
    have hrP : r = P⁻¹ *ᵥ Pi.single 0 1 := by
      rw [← hPr, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mulVec]
    have h00 : M⁻¹ 0 0 = Pi.single 0 1 ⬝ᵥ (M⁻¹ *ᵥ Pi.single 0 1) := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h00, hM, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← hrP]
  have hadjM : M.adjugate = M.det • M⁻¹ := by
    have hMu : IsUnit M.det := hMdet ▸ hS
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hMu, one_smul]
  rw [← hadj, hadjM, Matrix.smul_apply, hMinv, hMdet, smul_eq_mul]

end GEPPGrowth.Main.Prop416

open GEPPGrowth.Main GEPPGrowth.Main.Prop416 in
theorem solution (d : ℕ) (hd : 1 ≤ d) (S : Mat (d+1))
    (hS : S.PosDef) (y : Vec (d+1)) (hy : y ≠ 0)
    (i : Fin (d+1)) (hi : IsMaxPivot y i) :
    (updateAt S y i).det = S.det * (ratiosAt y i ⬝ᵥ (S⁻¹ *ᵥ ratiosAt y i)) ∧
    ((S-1).PosSemidef → (updateAt S y i).det ≤ ((d+1:ℕ):ℝ) * S.det) := by
  have hyi : y i ≠ 0 := by
    intro h0; apply hy; funext j
    have := hi j; rw [h0, abs_zero] at this; exact abs_nonpos_iff.1 this
  have hdet := hS.det_pos
  have hK := key S (isUnit_iff_ne_zero.2 hdet.ne') y i hyi
  refine ⟨hK, fun hPSD => ?_⟩
  rw [hK]
  set r := ratiosAt y i
  set u := S⁻¹ *ᵥ r
  set v := (S - 1) *ᵥ u
  have hru : r = u + v := by
    have hSu : S *ᵥ u = r := by
      simp only [u, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet.ne'),
        Matrix.one_mulVec]
    simp only [v, Matrix.sub_mulVec, Matrix.one_mulVec, hSu]
    abel
  have huv : 0 ≤ u ⬝ᵥ v := by
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hPSD).2 u
    simpa [v] using this
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
  have hrr : r ⬝ᵥ r ≤ ((d+1:ℕ):ℝ) := by
    have hle : ∀ j, r j * r j ≤ 1 := fun j => by
      have h1 : |r j| ≤ 1 := by
        simp only [r, ratiosAt, abs_div]
        exact (div_le_one (abs_pos.2 hyi)).2 (hi j)
      nlinarith [abs_mul_abs_self (r j), abs_nonneg (r j)]
    calc r ⬝ᵥ r = ∑ j, r j * r j := rfl
      _ ≤ ∑ _j : Fin (d+1), (1:ℝ) := Finset.sum_le_sum fun j _ => hle j
      _ = ((d+1:ℕ):ℝ) := by simp
  have : r ⬝ᵥ u ≤ ((d+1:ℕ):ℝ) := by
    have : r ⬝ᵥ r = r ⬝ᵥ u + (u ⬝ᵥ v + v ⬝ᵥ v) := by
      conv_lhs => rw [hru]
      conv_rhs => rw [hru]
      simp only [add_dotProduct, dotProduct_add, dotProduct_comm v u]
    linarith
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right this hdet.le
