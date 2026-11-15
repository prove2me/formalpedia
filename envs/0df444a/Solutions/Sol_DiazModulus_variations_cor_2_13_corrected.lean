-- Prove2me | solution 1 for DiazModulus.variations_cor_2_13_corrected
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:32.140203+00:00
-- url     : https://prove2.me/submissions/1fc174fd-afdc-487b-96ff-ede3c4f433a6

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_role_cor_6_3
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable

open Complex ComplexConjugate

/-! # Waldschmidt, *Variations* Cor. 2.13, with the corrected hypothesis and a repaired matrix

Write `conj Λ₁₁ = ε₁Λ₁₁` and `conj Λ₂₁ = ε₂Λ₂₁` with `ε₁, ε₂ ∈ {1, −1}`, and apply *Role* Cor. 6.3 to the `2 × 5`
matrix `N` with rows `(Λ₁₁, Λ₁₂, Λ₁₃, ε₂Λ̄₁₂, ε₂Λ̄₁₃)` and `(Λ₂₁, Λ₂₂, Λ₂₃, ε₁Λ̄₂₂, ε₁Λ̄₂₃)`. Its entries are in `ℒ̃`,
since `ℒ̃` is a `Q̄`-subspace stable under complex conjugation. The first column is `(Λ₁₁, Λ₂₁)`, so `1, N₁₁, N₂₁`
are `Q̄`-free. The seven columns of `(I₂, N)` are `Q̄`-free: the second row of a relation is an algebraic relation
among `1, Λ₂₁, Λ₂₂, Λ₂₃, Λ̄₂₂, Λ̄₂₃` (the last two coefficients multiplied by `ε₁ ≠ 0`), so these coefficients
vanish, and the first row then gives the last one. Cor. 6.3 makes one of `N₁₁N₂ⱼ − N₂₁N₁ⱼ`, `j = 2, …, 5`,
lie outside `ℒ̃`. For `j = 2, 3` these are `Λ₂ = Λ₁₁Λ₂₂ − Λ₂₁Λ₁₂` and `Λ₃ = Λ₁₁Λ₂₃ − Λ₂₁Λ₁₃`; for `j = 4, 5` they
are `(ε₁Λ₁₁)Λ̄₂ⱼ − (ε₂Λ₂₁)Λ̄₁ⱼ = conj Λ₂, conj Λ₃`. If `Λ₂, Λ₃ ∈ ℒ̃`, all four are in `ℒ̃`, a contradiction. (The
printed proof uses the columns `Λ̄₁ⱼ, Λ̄₂ⱼ` without the signs, which fails when one of `Λ₁₁, Λ₂₁` is real and the
other purely imaginary; the printed hypothesis "`Λ₂₁ ≠ 0`, `Λ₁₁/Λ₂₁` transcendental" is replaced by the freeness
of `1, Λ₁₁, Λ₂₁`, as in *Role* Cor. 6.3.) -/

namespace RC2_C213
open DiazModulus

/-- A sign `±1` as a nonzero element of `Q̄`. -/
theorem exists_sign (z : ℂ) (hz : conj z = z ∨ conj z = -z) :
    ∃ e : ↥Qbar, e ≠ 0 ∧ conj z = (e : ℂ) * z := by
  rcases hz with h | h
  · exact ⟨1, one_ne_zero, by simp [h]⟩
  · exact ⟨-1, by simp, by simp [h]⟩

theorem qbar_mul_mem (e : ↥Qbar) (x : ℂ) (hx : x ∈ LogAlgTilde) : (e : ℂ) * x ∈ LogAlgTilde := by
  have := LogAlgTilde.smul_mem e hx
  simpa [Subfield.smul_def] using this

end RC2_C213

open DiazModulus RC2_C213 in
theorem solution (M : Matrix (Fin 2) (Fin 3) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (h₁₁ : conj (M 0 0) = M 0 0 ∨ conj (M 0 0) = -M 0 0)
    (h₂₁ : conj (M 1 0) = M 1 0 ∨ conj (M 1 0) = -M 1 0)
    (h1 : LinearIndependent (↥Qbar) ![1, M 0 0, M 1 0])
    (h6 : LinearIndependent (↥Qbar) ![1, M 1 0, M 1 1, M 1 2, conj (M 1 1), conj (M 1 2)]) :
    M 0 0 * M 1 1 - M 1 0 * M 0 1 ∉ LogAlgTilde ∨ M 0 0 * M 1 2 - M 1 0 * M 0 2 ∉ LogAlgTilde := by
  have CJ := DiazModulus.logAlgTilde_conj_stable
  obtain ⟨e₁, he₁, hc₁⟩ := exists_sign _ h₁₁
  obtain ⟨e₂, -, hc₂⟩ := exists_sign _ h₂₁
  -- the repaired `2 × 5` matrix
  set N : Matrix (Fin 2) (Fin 5) ℂ :=
    !![M 0 0, M 0 1, M 0 2, (e₂ : ℂ) * conj (M 0 1), (e₂ : ℂ) * conj (M 0 2);
       M 1 0, M 1 1, M 1 2, (e₁ : ℂ) * conj (M 1 1), (e₁ : ℂ) * conj (M 1 2)] with hNdef
  have hN : ∀ i j, N i j ∈ LogAlgTilde := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [N] <;>
      first
      | exact hM _ _
      | exact qbar_mul_mem _ _ (CJ _ (hM _ _))
  have hN1 : LinearIndependent (↥Qbar) ![1, N 0 0, N 1 0] := by simpa [N] using h1
  -- the seven columns of `(I₂, N)` are `Q̄`-free: second row, then first row
  have hcol : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) N).col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have r0 := congrFun hg 0
    have r1 := congrFun hg 1
    simp [Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.col_apply, N, Subfield.smul_def,
      Matrix.one_apply] at r0 r1
    have key := (Fintype.linearIndependent_iff.mp h6)
      ![g (Sum.inl 1), g (Sum.inr 0), g (Sum.inr 1), g (Sum.inr 2), g (Sum.inr 3) * e₁, g (Sum.inr 4) * e₁]
      (by
        simp [Fin.sum_univ_succ, Subfield.smul_def]
        linear_combination r1)
    have k0 : g (Sum.inl 1) = 0 := by simpa using key 0
    have k1 : g (Sum.inr 0) = 0 := by simpa using key 1
    have k2 : g (Sum.inr 1) = 0 := by simpa using key 2
    have k3 : g (Sum.inr 2) = 0 := by simpa using key 3
    have k4 : g (Sum.inr 3) = 0 := by
      have := key 4; simp at this; exact this.resolve_right he₁
    have k5 : g (Sum.inr 4) = 0 := by
      have := key 5; simp at this; exact this.resolve_right he₁
    have k6 : g (Sum.inl 0) = 0 := by
      rw [k1, k2, k3, k4, k5] at r0
      simpa using r0
    intro i
    rcases i with i | i
    · fin_cases i
      · exact k6
      · exact k0
    · fin_cases i
      · exact k1
      · exact k2
      · exact k3
      · exact k4
      · exact k5
  obtain ⟨j, hj0, hj⟩ := DiazModulus.role_cor_6_3 N hN hN1 hcol
  by_contra hcon
  push Not at hcon
  obtain ⟨h2, h3⟩ := hcon
  -- the Cor. 6.3 numbers of columns 4 and 5 are `conj Λ₂`, `conj Λ₃`
  have c2 : conj (M 0 0 * M 1 1 - M 1 0 * M 0 1) =
      M 0 0 * ((e₁ : ℂ) * conj (M 1 1)) - M 1 0 * ((e₂ : ℂ) * conj (M 0 1)) := by
    rw [map_sub, map_mul, map_mul, hc₁, hc₂]; ring
  have c3 : conj (M 0 0 * M 1 2 - M 1 0 * M 0 2) =
      M 0 0 * ((e₁ : ℂ) * conj (M 1 2)) - M 1 0 * ((e₂ : ℂ) * conj (M 0 2)) := by
    rw [map_sub, map_mul, map_mul, hc₁, hc₂]; ring
  fin_cases j
  · exact hj0 rfl
  · exact hj (by simpa [N] using h2)
  · exact hj (by simpa [N] using h3)
  · exact hj (by simpa [N, ← c2] using CJ _ h2)
  · exact hj (by simpa [N, ← c3] using CJ _ h3)
