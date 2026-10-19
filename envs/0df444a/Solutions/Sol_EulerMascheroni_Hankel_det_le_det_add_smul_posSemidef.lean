-- Prove2me | solution 1 for EulerMascheroni.Hankel.det_le_det_add_smul_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:43:08.619811+00:00
-- url     : https://prove2.me/submissions/4d7b3a6c-d8ef-4a61-a66e-b9818749f6bd

import Mathlib
set_option autoImplicit false

open Matrix in
lemma det_one_add_posSemidef_ge_one {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) :
    1 ≤ (1 + P).det := by
  have hH := hP.isHermitian
  have hs := hH.spectral_theorem
  set U := hH.eigenvectorUnitary
  have hU : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have h1 : (1 + P) = (U : Matrix (Fin n) (Fin n) ℝ) *
      diagonal (fun i => 1 + hH.eigenvalues i) * star (U : Matrix (Fin n) (Fin n) ℝ) := by
    have h2 : (diagonal (fun i => 1 + hH.eigenvalues i) : Matrix (Fin n) (Fin n) ℝ) =
        1 + diagonal (fun i => hH.eigenvalues i) := by
      rw [← diagonal_one, ← diagonal_add]
    conv_lhs => rw [hs]
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU]
  have h3 : det (U : Matrix (Fin n) (Fin n) ℝ) * det (star (U : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
    rw [← det_mul, hU, det_one]
  have h4 : (1 + P).det = ∏ i, (1 + hH.eigenvalues i) := by
    rw [h1, det_mul, det_mul, det_diagonal]
    calc _ = (det (U : Matrix (Fin n) (Fin n) ℝ) * det (star (U : Matrix (Fin n) (Fin n) ℝ))) *
          ∏ i, (1 + hH.eigenvalues i) := by ring
      _ = _ := by rw [h3, one_mul]
  rw [h4]
  calc (1:ℝ) = ∏ _i : Fin n, (1:ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => by
        have := hP.eigenvalues_nonneg i
        linarith)

open Matrix MatrixOrder in
theorem solution {n : ℕ}
    (R S : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) (hS : S.PosSemidef)
    (g : ℝ) (hg : 0 < g) :
    R.det ≤ (R + g • S).det := by
  have hS0 : 0 ≤ S := hS.nonneg
  set B := CFC.sqrt S with hB
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS0
  have hBh : Bᴴ = B := (CFC.sqrt_nonneg S).isSelfAdjoint.star_eq
  have hdet : (R + g • S).det = R.det * (1 + B * R⁻¹ * (g • B)).det := by
    rw [← hBB, ← smul_mul_assoc]
    exact det_add_mul (g • B) B ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  have hM : (B * R⁻¹ * (g • B)) = g • (B * R⁻¹ * Bᴴ) := by
    rw [hBh, Matrix.mul_smul]
  have hP : (B * R⁻¹ * (g • B)).PosSemidef := by
    rw [hM]
    exact (hR.inv.posSemidef.mul_mul_conjTranspose_same B).smul hg.le
  have h1 := det_one_add_posSemidef_ge_one _ hP
  rw [hdet]
  have := hR.det_pos
  nlinarith
