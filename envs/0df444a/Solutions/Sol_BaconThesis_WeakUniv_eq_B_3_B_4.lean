-- Prove2me | solution 1 for BaconThesis.WeakUniv.eq_B_3_B_4
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:45:50.447102+00:00
-- url     : https://prove2.me/submissions/b6d0aaa4-5df5-4644-96f7-0c478ef4854d

import Mathlib
import Definitions.Def_BaconThesis_WeakUniv_lieAlg
import Definitions.Def_BaconThesis_WeakUniv_dfsProj

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BaconThesis.WeakUniv.SolB34

open BaconThesis.WeakUniv

/-- Basis states of two qubits, ordered `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def σ : (Fin 2 → Fin 2) ≃ Fin 4 := (piFinTwoEquiv fun _ => Fin 2).trans finProdFinEquiv

abbrev sub (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  M.submatrix σ σ

lemma sb_mul (M N : Matrix (Fin 4) (Fin 4) ℂ) : sub M * sub N = sub (M * N) :=
  Matrix.submatrix_mul_equiv _ _ _ _ _

lemma sb_sub (M N : Matrix (Fin 4) (Fin 4) ℂ) : sub M - sub N = sub (M - N) := rfl

lemma sb_smul (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) : c • sub M = sub (c • M) := rfl

lemma sb_inj {M N : Matrix (Fin 4) (Fin 4) ℂ} : sub M = sub N ↔ M = N := by
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (σ.symm i)) (σ.symm j)
    simpa using this
  · rintro rfl; rfl

lemma embed_eq (M : Matrix (Fin 4) (Fin 4) ℂ) :
    embed 2 0 1 (M.submatrix finProdFinEquiv finProdFinEquiv) = sub M := by
  ext x y
  have h : ∀ m : Fin 2, m ≠ 0 → m ≠ 1 → x m = y m := by
    intro m; fin_cases m <;> simp
  simp [embed, σ]

def E4 : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
def A4 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
def Y4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 0, 0, -Complex.I, 0; 0, Complex.I, 0, 0; 0, 0, 0, 0]
def Z4 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, -2, 0, 0; 0, 0, 2, 0; 0, 0, 0, 0]
def X4 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 4, 0; 0, 4, 0, 0; 0, 0, 0, 0]
def P4 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]

lemma hE : embed 2 0 1 exchange = sub E4 := by
  rw [exchange, embed_eq]; rfl

lemma hA : embed 2 0 1 (Tmat 0 0 1 0 0) = sub A4 := by
  rw [Tmat, embed_eq]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [A4]

lemma hY0 : embed 2 0 1 (Tmat 0 0 0 0 (-Complex.I)) = sub Y4 := by
  rw [Tmat, embed_eq]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Y4]

lemma hP : dfsProj 2 1 = sub P4 := by
  ext x y
  obtain ⟨p, rfl⟩ := σ.symm.surjective x
  obtain ⟨q, rfl⟩ := σ.symm.surjective y
  simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  fin_cases p <;> fin_cases q <;> simp [dfsProj, P4, σ, Matrix.diagonal_apply] <;> decide

lemma kY : Complex.I • (A4 * E4 - E4 * A4) = Y4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A4, E4, Y4]

lemma kZ : Complex.I • (E4 * Y4 - Y4 * E4) = Z4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Z4, E4, Y4] <;> ring_nf <;> simp

lemma kX : Complex.I • (Y4 * Z4 - Z4 * Y4) = X4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Z4, X4, Y4] <;> ring_nf <;> simp

lemma kP (M : Matrix (Fin 4) (Fin 4) ℂ) (h1 : ∀ j, M 0 j = 0) (h2 : ∀ j, M 3 j = 0)
    (h3 : ∀ i, M i 0 = 0) (h4 : ∀ i, M i 3 = 0) : P4 * M * P4 = M := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [P4, h1, h2, h3, h4]

lemma lie_eq (P Q : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    Complex.I • (Complex.I • (P * Q - Q * P)) = ⁅Complex.I • P, Complex.I • Q⁆ := by
  rw [Ring.lie_def, smul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_smul, ← smul_sub]

lemma span_hermitian (H : Matrix (Fin 4) (Fin 4) ℂ) (hH : H.IsHermitian)
    (hPH : P4 * H * P4 = H) (htr : H.trace = 0) :
    ∃ a b c : ℝ, H = (a : ℂ) • X4 + (b : ℂ) • Y4 + (c : ℂ) • Z4 := by
  have he : ∀ i j, star (H j i) = H i j := fun i j => by
    simpa using congrFun (congrFun hH i) j
  have hent : ∀ i j, H i j = (P4 * H * P4) i j := fun i j => by rw [hPH]
  simp only [P4, Matrix.mul_apply, Fin.sum_univ_four] at hent
  have h11 := he 1 1
  have h22 := he 2 2
  have h21 := he 2 1
  have htr' : H 0 0 + H 1 1 + H 2 2 + H 3 3 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_four] using htr
  have z : ∀ i j, (i = 0 ∨ i = 3 ∨ j = 0 ∨ j = 3) → H i j = 0 := by
    intro i j hij
    rw [hent i j]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  have h00 := z 0 0 (by simp)
  have h33 := z 3 3 (by simp)
  rw [h00, h33] at htr'
  have hr1 : ((H 1 1).re : ℂ) = H 1 1 := by
    apply Complex.ext <;> simp
    have := congrArg Complex.im h11
    simp at this; linarith
  refine ⟨(H 1 2).re / 4, -(H 1 2).im, -(H 1 1).re / 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X4, Y4, Z4, z]
  · exact hr1.symm
  · rw [← h21]; apply Complex.ext <;> simp
  · rw [hr1]; linear_combination htr'

end BaconThesis.WeakUniv.SolB34

open BaconThesis.WeakUniv BaconThesis.WeakUniv.SolB34 in
theorem solution :
    let E := embed 2 0 1 exchange
    let A := embed 2 0 1 (Tmat 0 0 1 0 0)
    let Y := Complex.I • (A * E - E * A)
    let Z := Complex.I • (E * Y - Y * E)
    let X := Complex.I • (Y * Z - Z * Y)
    Y = embed 2 0 1 (Tmat 0 0 0 0 (-Complex.I)) ∧
    (Complex.I • X ∈ lieAlg 2 ∧ Complex.I • Y ∈ lieAlg 2 ∧ Complex.I • Z ∈ lieAlg 2) ∧
    (dfsProj 2 1 * X * dfsProj 2 1 = X ∧ dfsProj 2 1 * Y * dfsProj 2 1 = Y ∧
      dfsProj 2 1 * Z * dfsProj 2 1 = Z) ∧
    (∀ H : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ, H.IsHermitian →
      dfsProj 2 1 * H * dfsProj 2 1 = H → H.trace = 0 →
      ∃ a b c : ℝ, H = (a : ℂ) • X + (b : ℂ) • Y + (c : ℂ) • Z) := by
  intro E A Y Z X
  have hEm : Complex.I • E ∈ lieAlg 2 :=
    LieSubalgebra.subset_lieSpan ⟨_, ⟨0, by norm_num, Or.inl rfl⟩, rfl⟩
  have hAm : Complex.I • A ∈ lieAlg 2 :=
    LieSubalgebra.subset_lieSpan ⟨_, ⟨0, by norm_num, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩
  have hYm : Complex.I • Y ∈ lieAlg 2 := by
    show Complex.I • (Complex.I • (A * E - E * A)) ∈ lieAlg 2
    rw [lie_eq]; exact (lieAlg 2).lie_mem hAm hEm
  have hZm : Complex.I • Z ∈ lieAlg 2 := by
    show Complex.I • (Complex.I • (E * Y - Y * E)) ∈ lieAlg 2
    rw [lie_eq]; exact (lieAlg 2).lie_mem hEm hYm
  have hXm : Complex.I • X ∈ lieAlg 2 := by
    show Complex.I • (Complex.I • (Y * Z - Z * Y)) ∈ lieAlg 2
    rw [lie_eq]; exact (lieAlg 2).lie_mem hYm hZm
  have hY : Y = sub Y4 := by
    show Complex.I • (A * E - E * A) = _
    simp only [A, E, hA, hE, sb_mul, sb_sub, sb_smul, kY]
  have hZ : Z = sub Z4 := by
    show Complex.I • (E * Y - Y * E) = _
    simp only [E, hE, hY, sb_mul, sb_sub, sb_smul, kZ]
  have hX : X = sub X4 := by
    show Complex.I • (Y * Z - Z * Y) = _
    simp only [hY, hZ, sb_mul, sb_sub, sb_smul, kX]
  refine ⟨hY.trans hY0.symm, ⟨hXm, hYm, hZm⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hX, hP, sb_mul, sb_mul, kP] <;> intro k <;> fin_cases k <;> simp [X4]
  · rw [hY, hP, sb_mul, sb_mul, kP] <;> intro k <;> fin_cases k <;> simp [Y4]
  · rw [hZ, hP, sb_mul, sb_mul, kP] <;> intro k <;> fin_cases k <;> simp [Z4]
  · intro H hH hPH htr
    set H4 : Matrix (Fin 4) (Fin 4) ℂ := H.submatrix σ.symm σ.symm with hH4
    have hHs : H = sub H4 := by ext x y; simp [H4]
    rw [hHs] at hH hPH htr
    have hH' : H4.IsHermitian := sb_inj.mp (by
      show (Matrix.conjTranspose H4).submatrix σ σ = H4.submatrix σ σ
      rw [← Matrix.conjTranspose_submatrix]; exact hH)
    have hPH' : P4 * H4 * P4 = H4 := by rw [← sb_inj, ← sb_mul, ← sb_mul, ← hP, hPH]
    have htr' : H4.trace = 0 := by
      rw [← htr]; simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
      exact (Equiv.sum_comp σ fun i => H4 i i).symm
    obtain ⟨a, b, c, habc⟩ := span_hermitian H4 hH' hPH' htr'
    refine ⟨a, b, c, ?_⟩
    rw [hHs, hX, hY, hZ, habc]
    rfl
