-- Prove2me | solution 1 for DiazModulus.dalag_cor_12_24
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:21.552544+00:00
-- url     : https://prove2.me/submissions/06f5f225-ffdd-402a-83e6-af8790e4fe9d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rank_bound

open Complex ComplexConjugate

/-! # DALAG Corollary 12.24: rank at least two, from Roy's Corollary 1

The hypothesis `dℓ > d + ℓ` forces `d, ℓ ≥ 2`. Suppose `rank M ≤ 1`. Roy's Corollary 1 (DALAG Th. 12.20)
gives `P ∈ GL_d(Q̄)`, `Q ∈ GL_ℓ(Q̄)`, `1 ≤ d' ≤ d`, `ℓ' ≤ ℓ` with `(PMQ)ᵢⱼ = 0` for `i < d'`, `j ≥ ℓ'`, and
`dℓ' ≤ rank(M)(d' + ℓ') ≤ d' + ℓ'`. Let `N = PMQ`. No row of `N` is zero: otherwise, `Q` being invertible,
`Σₐ P_{ia} Mₐ = 0` with algebraic coefficients, so the `i`-th row of `P` vanishes since the rows of `M` are free
over `Q̄`, and `det P = 0`. Transposing, no column of `N` is zero. If `ℓ' = ℓ`, then `dℓ ≤ d' + ℓ ≤ d + ℓ`,
a contradiction. If `ℓ' = 0`, the first row of `N` is zero. Otherwise the last column `j₁ ≥ ℓ'` of `N`
vanishes in the rows `< d'` but not everywhere, so some row `i₁ ≥ d'` has `N_{i₁j₁} ≠ 0`, while the first
row of `N` is non-zero and vanishes at `j₁`; these two rows are linearly independent, so
`rank M = rank N ≥ 2`, a contradiction. This direct route does not pass through Corollary 12.22. -/

namespace RC3_C24
open DiazModulus Matrix

/-- No row of `PMQ` vanishes when the rows of `M` are free over `Q̄`. -/
theorem row_ne {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hrows : LinearIndependent (↥Qbar) M.row)
    (P : Matrix (Fin d) (Fin d) ℂ) (Q : Matrix (Fin l) (Fin l) ℂ) (hP : IsUnit P.det)
    (hQ : IsUnit Q.det) (hPa : ∀ i j, P i j ∈ Qbar) (i : Fin d) : ∃ j, (P * M * Q) i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hPM : ∀ j, (P * M) i j = 0 := by
    intro j
    rw [← Matrix.mul_nonsing_inv_cancel_right Q (P * M) hQ, Matrix.mul_apply]
    simp [hcon]
  have hrel : ∑ a, (⟨P i a, hPa i a⟩ : ↥Qbar) • M.row a = 0 := by
    ext j
    rw [Pi.zero_apply, ← hPM j, Matrix.mul_apply]
    simp [Finset.sum_apply, Subfield.smul_def, Matrix.row]
  have h0 := Fintype.linearIndependent_iff.mp hrows _ hrel
  exact hP.ne_zero (Matrix.det_eq_zero_of_row_eq_zero i fun a => congrArg Subtype.val (h0 a))

/-- No column of `PMQ` vanishes when the columns of `M` are free over `Q̄`. -/
theorem col_ne {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hcols : LinearIndependent (↥Qbar) M.col)
    (P : Matrix (Fin d) (Fin d) ℂ) (Q : Matrix (Fin l) (Fin l) ℂ) (hP : IsUnit P.det)
    (hQ : IsUnit Q.det) (hQa : ∀ i j, Q i j ∈ Qbar) (j : Fin l) : ∃ i, (P * M * Q) i j ≠ 0 := by
  have hT : (P * M * Q)ᵀ = Qᵀ * Mᵀ * Pᵀ := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨i, hi⟩ := row_ne Mᵀ hcols Qᵀ Pᵀ (by rwa [Matrix.det_transpose])
    (by rwa [Matrix.det_transpose]) (fun a b => hQa b a) j
  refine ⟨i, fun h => hi ?_⟩
  rw [← hT, Matrix.transpose_apply, h]

/-- Two rows, one vanishing at `j₁` and non-zero somewhere, the other non-zero at `j₁`, give rank `≥ 2`. -/
theorem two_le_rank {d l : ℕ} (N : Matrix (Fin d) (Fin l) ℂ) (i₀ i₁ : Fin d) (j₀ j₁ : Fin l)
    (h00 : N i₀ j₀ ≠ 0) (h01 : N i₀ j₁ = 0) (h11 : N i₁ j₁ ≠ 0) : 2 ≤ N.rank := by
  have hrow : (N.submatrix ![i₀, i₁] id).row = ![N.row i₀, N.row i₁] := by
    ext k j; fin_cases k <;> rfl
  have hli : LinearIndependent ℂ (N.submatrix ![i₀, i₁] id).row := by
    rw [hrow, LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrFun hst j₁
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.row, h01, mul_zero, zero_add,
      Pi.zero_apply] at e1
    have ht : t = 0 := (mul_eq_zero.mp e1).resolve_right h11
    subst ht
    have e0 := congrFun hst j₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.row, zero_mul, add_zero,
      Pi.zero_apply] at e0
    exact ⟨(mul_eq_zero.mp e0).resolve_right h00, rfl⟩
  have := Matrix.rank_submatrix_le N ![i₀, i₁] id
  rw [hli.rank_matrix, Fintype.card_fin] at this
  exact this

end RC3_C24

open DiazModulus RC3_C24 in
theorem solution {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hrows : LinearIndependent (↥Qbar) M.row) (hcols : LinearIndependent (↥Qbar) M.col)
    (hdl : l + d < l * d) : 2 ≤ M.rank := by
  have hd : 2 ≤ d := by
    rcases d with _ | _ | d
    · simp at hdl
    · simp at hdl
    · omega
  have hl : 2 ≤ l := by
    rcases l with _ | _ | l
    · simp at hdl
    · simp at hdl
    · omega
  by_contra hlt
  push Not at hlt
  obtain ⟨d', l', P, Q, hd'0, hd'd, hl'l, hP, hQ, hPa, hQa, hz, hineq⟩ :=
    DiazModulus.roy_rank_bound M hM (by omega)
  have hNr : (P * M * Q).rank = M.rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]
  have hineq' : d * l' ≤ d' + l' := by
    have h1 : M.rank ≤ 1 := by omega
    calc d * l' ≤ M.rank * (d' + l') := hineq
      _ ≤ 1 * (d' + l') := Nat.mul_le_mul_right _ h1
      _ = d' + l' := one_mul _
  let i₀ : Fin d := ⟨0, by omega⟩
  rcases (show l' = l ∨ l' = 0 ∨ (0 < l' ∧ l' < l) by omega) with h | h | ⟨h1, h2⟩
  · subst h
    nlinarith
  · subst h
    obtain ⟨j, hj⟩ := row_ne M hrows P Q hP hQ hPa i₀
    exact hj (hz _ _ hd'0 (Nat.zero_le _))
  · let j₁ : Fin l := ⟨l - 1, by omega⟩
    obtain ⟨i₁, hi₁⟩ := col_ne M hcols P Q hP hQ hQa j₁
    obtain ⟨j₀, hj₀⟩ := row_ne M hrows P Q hP hQ hPa i₀
    have h01 : (P * M * Q) i₀ j₁ = 0 := hz _ _ hd'0 (by simp [j₁]; omega)
    have := two_le_rank (P * M * Q) i₀ i₁ j₀ j₁ hj₀ h01 hi₁
    omega
