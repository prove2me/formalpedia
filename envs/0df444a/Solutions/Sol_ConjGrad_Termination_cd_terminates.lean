-- Prove2me | solution 1 for ConjGrad.Termination.cd_terminates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:54:25.992988+00:00
-- url     : https://prove2.me/submissions/cf71c2d4-5ca2-4978-8410-0bfd297516d1

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun

open Matrix

namespace ConjGrad.Termination

theorem aux_cgt_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  have hT : Aᵀ = A := by
    have := hA.isHermitian
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

theorem aux_cgt_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ (A *ᵥ v) := by
  simpa using hA.dotProduct_mulVec_pos hv

theorem aux_cgt_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (v : Fin n → ℝ) (hv : v ⬝ᵥ (A *ᵥ v) = 0) : v = 0 := by
  by_contra h
  have := aux_cgt_pos A hA v h
  linarith

theorem aux_cgt_rstep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) (i : ℕ) :
    r (i + 1) = r i - ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) • (A *ᵥ p i) := by
  rw [hcd.residual (i + 1), hcd.step, Matrix.mulVec_add, Matrix.mulVec_smul, ← sub_sub,
    ← hcd.residual i]

theorem aux_cgt_orth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) :
    ∀ i, ∀ j < i, p j ⬝ᵥ r i = 0 := by
  intro i
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    intro j hj
    rw [aux_cgt_rstep A k x r p hcd i, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · rw [ih j hlt]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [aux_cgt_symm A hA (p j), hcd.conj i' j (by omega)]
      simp
    · subst heq
      by_cases h0 : p j ⬝ᵥ (A *ᵥ p j) = 0
      · have := aux_cgt_zero A hA _ h0
        simp [this]
      · field_simp
        ring

end ConjGrad.Termination

open ConjGrad.Termination
open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p)
    (hp : ∀ i < n, p i ≠ 0) :
    ∃ m ≤ n, x m = h := by
  refine ⟨n, le_rfl, ?_⟩
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun j => p j with hPdef
  have hPAP : P * A * Pᵀ = Matrix.diagonal (fun i : Fin n => p i ⬝ᵥ (A *ᵥ p i)) := by
    ext i j
    have e : (P * A * Pᵀ) i j = p i ⬝ᵥ (A *ᵥ p j) := by
      simp only [hPdef, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
        dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with hlt | hlt
      · obtain ⟨j', hj'⟩ : ∃ j', (j : ℕ) = j' + 1 := ⟨(j : ℕ) - 1, by omega⟩
        rw [aux_cgt_symm A hA]
        have := hcd.conj j' i (by omega)
        rw [← hj'] at this
        exact this
      · obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
        have := hcd.conj i' j (by omega)
        rw [← hi'] at this
        exact this
  have hdet : P.det ≠ 0 := by
    have h1 : (P * A * Pᵀ).det ≠ 0 := by
      rw [hPAP, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        (aux_cgt_pos A hA (p i) (hp i i.isLt)).ne'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    intro h0
    apply h1
    rw [h0]; ring
  have hr : r n = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    ext j
    simp only [hPdef, Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
    exact aux_cgt_orth A hA k x r p hcd n j j.isLt
  have hAdet : A.det ≠ 0 := (hA.isUnit.map Matrix.detMonoidHom).ne_zero
  have hx : A *ᵥ (x n - h) = 0 := by
    rw [Matrix.mulVec_sub, hh]
    have := hcd.residual n
    rw [hr] at this
    rw [eq_comm, sub_eq_zero] at this
    rw [sub_eq_zero]
    exact this.symm
  have := Matrix.eq_zero_of_mulVec_eq_zero hAdet hx
  exact sub_eq_zero.mp this
