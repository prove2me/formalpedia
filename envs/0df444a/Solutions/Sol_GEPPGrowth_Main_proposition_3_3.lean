-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:48:12.811046+00:00
-- url     : https://prove2.me/submissions/d485805d-7cca-4703-b540-a969a83f23ae

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace GEPPGrowth.Main.Prop33

open GEPPGrowth.Main

/-- `D Dᵀ = 1`: the rows of the deletion matrix are distinct standard basis rows. -/
private lemma deletion_mul_transpose {d : ℕ} (i : Fin (d+1)) :
    deletion i * (deletion i).transpose = 1 := by
  ext a b
  simp [Matrix.mul_apply, deletion, Matrix.one_apply, eq_comm]

/-- `Dᵀ D = 1 - eᵢ eᵢᵀ`: the projection that kills coordinate `i`. -/
private lemma transpose_mul_deletion {d : ℕ} (i : Fin (d+1)) :
    (deletion i).transpose * deletion i =
      1 - Matrix.vecMulVec (basisVector i) (basisVector i) := by
  have key : ∀ g : Fin (d+1) → ℝ,
      ∑ a : Fin d, g (Equiv.swap 0 i a.succ) = ∑ k, g k - g i := by
    intro g
    rw [← Equiv.sum_comp (Equiv.swap 0 i) g, Fin.sum_univ_succ, Equiv.swap_apply_left]
    ring
  refine Matrix.ext fun b c => ?_
  have := key (fun k => (if k = b then 1 else 0) * (if k = c then 1 else 0))
  rw [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  simp only [Matrix.transpose_apply, deletion]
  rw [this]
  simp only [basisVector]
  by_cases hb : b = i <;> by_cases hc : c = i <;> by_cases hbc : b = c <;>
    simp only [hb, hc, hbc, eq_comm (a := i)] <;> subst_vars <;>
    simp_all [Finset.sum_ite_eq'] <;> exact fun h => by simp_all

/-- The `i`-th row of `I - r eᵢᵀ` vanishes when `rᵢ = 1`, so `(1 - eᵢeᵢᵀ) E = E`. -/
private lemma proj_mul_elim {d : ℕ} (y : Vec (d+1)) (i : Fin (d+1)) (hyi : y i ≠ 0) :
    (1 - Matrix.vecMulVec (basisVector i) (basisVector i)) * eliminationAt y i =
      eliminationAt y i := by
  ext a b
  by_cases ha : a = i
  · subst ha
    simp only [Matrix.mul_apply, eliminationAt, Matrix.vecMulVec_apply, basisVector, ratiosAt,
      Matrix.one_apply, Matrix.sub_apply]
    rw [Finset.sum_eq_zero fun x _ => by by_cases h : a = x <;> simp [h, eq_comm]]
    by_cases hab : a = b
    · subst hab; simp [hyi]
    · simp [hab, Ne.symm hab]
  · simp [Matrix.mul_apply, eliminationAt, Matrix.vecMulVec_apply, basisVector, ratiosAt,
      Matrix.one_apply, Matrix.sub_apply, ha]

/-- A matrix with `D Dᵀ = 1` has spectral norm at most one, and so does its transpose. -/
private lemma norm_le_one_of_mul_transpose {m n : ℕ} (D : Matrix (Fin m) (Fin (n)) ℝ)
    (h : D * D.transpose = 1) : ‖D‖ ≤ 1 ∧ ‖D.transpose‖ ≤ 1 := by
  have h1 : ‖(1 : Matrix (Fin m) (Fin m) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hsq : ‖D.transpose‖ * ‖D.transpose‖ ≤ 1 := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self D.transpose
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose, h] at this
    rw [← this]; exact h1
  have ht : ‖D.transpose‖ ≤ 1 := by nlinarith [norm_nonneg D.transpose]
  refine ⟨?_, ht⟩
  have := Matrix.l2_opNorm_conjTranspose D
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [← this]; exact ht

end GEPPGrowth.Main.Prop33

open GEPPGrowth.Main GEPPGrowth.Main.Prop33 in
theorem solution (d : ℕ) (S : Mat (d+1)) (hS : S.PosSemidef)
    (y : Vec (d+1)) (hy : y ≠ 0) (i : Fin (d+1)) (hi : IsMaxPivot y i) :
    GaussianMatrix.specNorm (updateAt S y i) =
      GaussianMatrix.specNorm (eliminationAt y i * S * (eliminationAt y i).transpose) := by
  have hyi : y i ≠ 0 := by
    intro h0; apply hy; funext j
    have := hi j; rw [h0, abs_zero] at this; exact abs_nonpos_iff.1 this
  set D := deletion i
  set E := eliminationAt y i
  set M := E * S * E.transpose
  have hU : updateAt S y i = D * M * D.transpose := by
    simp only [updateAt, compressionAt, M, Matrix.transpose_mul, Matrix.mul_assoc]; rfl
  have hM : D.transpose * (D * M * D.transpose) * D = M := by
    have hPE : D.transpose * D * E = E := by rw [transpose_mul_deletion]; exact proj_mul_elim y i hyi
    have hEP : E.transpose * (D.transpose * D) = E.transpose := by
      have := congrArg Matrix.transpose hPE
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    calc D.transpose * (D * M * D.transpose) * D
        = (D.transpose * D * E) * S * (E.transpose * (D.transpose * D)) := by
          simp only [M, Matrix.mul_assoc]
      _ = M := by rw [hPE, hEP]
  obtain ⟨hD, hDt⟩ := norm_le_one_of_mul_transpose D (deletion_mul_transpose i)
  unfold GaussianMatrix.specNorm
  rw [hU]
  apply le_antisymm
  · calc ‖D * M * D.transpose‖ ≤ ‖D‖ * ‖M‖ * ‖D.transpose‖ := by
          refine (Matrix.l2_opNorm_mul _ _).trans ?_
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖M‖ * 1 := by gcongr
      _ = ‖M‖ := by ring
  · calc ‖M‖ = ‖D.transpose * (D * M * D.transpose) * D‖ := by rw [hM]
      _ ≤ ‖D.transpose‖ * ‖D * M * D.transpose‖ * ‖D‖ := by
          refine (Matrix.l2_opNorm_mul _ _).trans ?_
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖D * M * D.transpose‖ * 1 := by gcongr
      _ = ‖D * M * D.transpose‖ := by ring
