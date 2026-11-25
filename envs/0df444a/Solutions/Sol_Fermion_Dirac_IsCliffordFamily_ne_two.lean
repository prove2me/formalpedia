-- Prove2me | solution 1 for Fermion.Dirac.IsCliffordFamily.ne_two
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:34:08.611751+00:00
-- url     : https://prove2.me/submissions/312dd0ee-f543-4c60-ac56-b999c6bf0c73

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily

open Matrix Complex Fermion.Dirac

/-- Diagonal Minkowski entries are `±1`, off-diagonal ones vanish. -/
lemma mink_diag (μ : Fin 1 ⊕ Fin 3) : (minkowskiMatrix (d := 3) μ μ : ℂ) ≠ 0 := by
  rcases μ with i | i <;> simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

lemma mink_off {μ ν : Fin 1 ⊕ Fin 3} (h : μ ≠ ν) : (minkowskiMatrix (d := 3) μ ν : ℂ) = 0 := by
  simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.diagonal_apply_ne _ h]

lemma cliff_sq {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) (μ : Fin 1 ⊕ Fin 3) :
    γ μ * γ μ = (minkowskiMatrix (d := 3) μ μ : ℂ) • 1 := by
  have h := hγ μ μ
  rw [← two_smul ℂ (γ μ * γ μ), mul_smul] at h
  exact smul_right_injective _ two_ne_zero h

lemma cliff_anti {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) {μ ν : Fin 1 ⊕ Fin 3} (h : μ ≠ ν) :
    γ μ * γ ν + γ ν * γ μ = 0 := by
  rw [hγ μ ν, mink_off h]; simp

lemma exists_ne' (μ : Fin 1 ⊕ Fin 3) : ∃ ν, ν ≠ μ := by
  rcases μ with i | i
  · exact ⟨Sum.inr 0, by simp⟩
  · exact ⟨Sum.inl 0, by simp⟩

lemma trace_gamma {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) (μ : Fin 1 ⊕ Fin 3) : (γ μ).trace = 0 := by
  obtain ⟨ν, hν⟩ := exists_ne' μ
  set c : ℂ := (minkowskiMatrix (d := 3) ν ν : ℂ)
  have hc : c ≠ 0 := mink_diag ν
  have hsq := cliff_sq hγ ν
  have hanti : γ ν * γ μ = -(γ μ * γ ν) := eq_neg_of_add_eq_zero_left (by
    rw [add_comm]; exact cliff_anti hγ hν.symm)
  have h1 : (γ μ * (γ ν * γ ν)).trace = c * (γ μ).trace := by
    rw [hsq, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  have h2 : (γ μ * (γ ν * γ ν)).trace = -(c * (γ μ).trace) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hanti, Matrix.neg_mul,
      Matrix.trace_neg, Matrix.mul_assoc, hsq, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      smul_eq_mul]
  have : c * (γ μ).trace = 0 := by linear_combination (h2 - h1) / 2
  exact (mul_eq_zero.mp this).resolve_left hc

lemma trace_mul_ne {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) {μ ν : Fin 1 ⊕ Fin 3} (h : μ ≠ ν) : (γ μ * γ ν).trace = 0 := by
  have := congrArg Matrix.trace (cliff_anti hγ h)
  rw [Matrix.trace_add, Matrix.trace_mul_comm (γ ν), Matrix.trace_zero] at this
  linear_combination this / 2

/-- The five matrices `1, γ^0, …, γ^3` are linearly independent when `n ≠ 0`. -/
lemma five_le {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) (hn : n ≠ 0) : 5 ≤ n * n := by
  let v : Option (Fin 1 ⊕ Fin 3) → Matrix (Fin n) (Fin n) ℂ := fun o => o.elim 1 γ
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have htr : ∀ i j, (v i * v j).trace = if i = j then (if i = none then (n : ℂ) else
      (minkowskiMatrix (d := 3) (i.getD (Sum.inl 0)) (i.getD (Sum.inl 0)) : ℂ) * n) else 0 := by
    intro i j
    rcases i with _ | μ <;> rcases j with _ | ν
    · simp [v]
    · simp [v, trace_gamma hγ]
    · simp [v, trace_gamma hγ]
    · by_cases h : μ = ν
      · subst h; simp [v, cliff_sq hγ, Matrix.trace_smul]
      · simp [v, trace_mul_ne hγ h, h]
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun M => (M * v j).trace) hg
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.zero_mul, Matrix.trace_zero, htr] at this
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rcases j with _ | μ
    · simpa [hnC] using this
    · simpa [hnC, mink_diag μ] using this
  have := hli.fintype_card_le_finrank
  simpa [Module.finrank_matrix] using this

theorem solution {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) : n ≠ 2 := by
  rintro rfl
  have := five_le hγ (by norm_num)
  norm_num at this
