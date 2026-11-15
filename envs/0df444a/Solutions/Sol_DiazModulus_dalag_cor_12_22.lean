-- Prove2me | solution 1 for DiazModulus.dalag_cor_12_22
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:18.966195+00:00
-- url     : https://prove2.me/submissions/c42c8ac5-de90-4604-a90e-a097bb6b30b5

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rank_bound
import Theorems.Thm_DiazModulus_matrix_rank_le_of_zero_block

open Complex ComplexConjugate

/-! # DALAG Corollary 12.22: the rank is at least half the structural rank

Write `M = Σₖ eₖ Nₖ` with `e` free over `Q̄` and algebraic matrices `Nₖ`, and let `N(X) = Σₖ Xₖ Nₖ` over
`Q̄(X₁, …, X_m)`, of rank `r`. If `r = 0` there is nothing to prove. Otherwise choose `r` rows `I` of `N(X)`
that are linearly independent; the row submatrix `M_I` has entries in `ℒ̃`. Roy's Corollary 1 for `M_I`
gives `P ∈ GL_r(Q̄)`, `Q ∈ GL_ℓ(Q̄)` and `1 ≤ d' ≤ r`, `ℓ'` with `(P M_I Q)ᵢⱼ = 0` for `i < d'`, `j ≥ ℓ'`,
and `rℓ' ≤ rank(M_I)(d' + ℓ')`. Since `(P M_I Q)ᵢⱼ = Σₖ eₖ (P (N_k)_I Q)ᵢⱼ` with algebraic coefficients and
`e` is free over `Q̄`, every `(P (N_k)_I Q)ᵢⱼ` vanishes in that block, so `P N(X)_I Q` has the same zero
block. It has rank `r` (`P`, `Q` invertible over `Q̄`), so the zero block bound gives `r + d' ≤ r + ℓ'`,
that is `d' ≤ ℓ'`. Then `rℓ' ≤ rank(M_I)·2ℓ'` with `ℓ' ≥ 1`, so `r ≤ 2 rank(M_I) ≤ 2 rank(M)`. The argument
uses only that `Q̄ → Q̄(X)` is a field embedding, not that the `Xₖ` are variables. -/

namespace RC3_C22
open DiazModulus

/-- Row selection: `rank A` linearly independent rows of `A`. -/
theorem exists_indep_rows {K : Type*} [Field K] {d l : ℕ} (A : Matrix (Fin d) (Fin l) K) :
    ∃ I : Fin A.rank → Fin d, LinearIndependent K (A.submatrix I id).row := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  have hcard : Fintype.card κ = A.rank := by
    rw [Matrix.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨a ∘ σ, hli.comp σ σ.injective⟩

/-- Conjugating a presentation by matrices over `Q̄`. -/
theorem conj_sum {R : Type*} [CommRing R] (φ : ↥Qbar →+* R) {r l m : ℕ} (c : Fin m → R)
    (A : Fin m → Matrix (Fin r) (Fin l) ↥Qbar) (P : Matrix (Fin r) (Fin r) ↥Qbar)
    (Q : Matrix (Fin l) (Fin l) ↥Qbar) :
    P.map φ * (∑ k, c k • (A k).map φ) * Q.map φ = ∑ k, c k • (P * A k * Q).map φ := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, Matrix.map_mul]

/-- Row submatrix of a presentation. -/
theorem sub_sum {R : Type*} [CommRing R] (φ : ↥Qbar →+* R) {r d l m : ℕ} (c : Fin m → R)
    (A : Fin m → Matrix (Fin d) (Fin l) ↥Qbar) (I : Fin r → Fin d) :
    (∑ k, c k • (A k).map φ).submatrix I id = ∑ k, c k • ((A k).submatrix I id).map φ := by
  ext i j
  simp [Matrix.sum_apply]

theorem det_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : (A.map f).det = f A.det :=
  (RingHom.map_det f A).symm

/-- The corollary for any field embedding `g : Q̄ → K` and any specialisation `c` of the variables. -/
theorem main {K : Type*} [Field K] (g : ↥Qbar →+* K) {d l m : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlgTilde) (e : Fin m → ℂ) (he : LinearIndependent (↥Qbar) e)
    (N : Fin m → Matrix (Fin d) (Fin l) ↥Qbar) (hMN : M = ∑ k, e k • (N k).map Qbar.subtype)
    (c : Fin m → K) : (∑ k, c k • (N k).map g).rank ≤ 2 * M.rank := by
  classical
  set NX := ∑ k, c k • (N k).map g with hNX
  obtain ⟨I, hI⟩ := exists_indep_rows NX
  have hrI : (NX.submatrix I id).rank = NX.rank := by
    rw [hI.rank_matrix, Fintype.card_fin]
  generalize hrdef : NX.rank = r at I hI hrI ⊢
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · rw [h0]; exact Nat.zero_le _
  set MI := M.submatrix I id with hMI
  have hMI' : MI = ∑ k, e k • ((N k).submatrix I id).map Qbar.subtype := by
    rw [hMI, hMN]; exact sub_sum _ _ _ _
  obtain ⟨d', l', P, Q, hd'0, hd'r, hl'l, hP, hQ, hPa, hQa, hz, hineq⟩ :=
    DiazModulus.roy_rank_bound MI (fun i j => hM _ _) hr
  let P' : Matrix (Fin r) (Fin r) ↥Qbar := fun i j => ⟨P i j, hPa i j⟩
  let Q' : Matrix (Fin l) (Fin l) ↥Qbar := fun i j => ⟨Q i j, hQa i j⟩
  have hPP : P'.map Qbar.subtype = P := by ext i j; rfl
  have hQQ : Q'.map Qbar.subtype = Q := by ext i j; rfl
  have hPdet : IsUnit P'.det := by
    refine isUnit_iff_ne_zero.mpr fun h => hP.ne_zero ?_
    rw [← hPP, det_map, h, map_zero]
  have hQdet : IsUnit Q'.det := by
    refine isUnit_iff_ne_zero.mpr fun h => hQ.ne_zero ?_
    rw [← hQQ, det_map, h, map_zero]
  set T : Fin m → Matrix (Fin r) (Fin l) ↥Qbar := fun k => P' * (N k).submatrix I id * Q' with hT
  have hPMQ : P * MI * Q = ∑ k, e k • (T k).map Qbar.subtype := by
    calc P * MI * Q = P'.map Qbar.subtype * (∑ k, e k • ((N k).submatrix I id).map Qbar.subtype) *
          Q'.map Qbar.subtype := by rw [hPP, hQQ, hMI']
      _ = _ := conj_sum _ _ _ _ _
  -- S1: the zero block passes to every `Nₖ`, by freeness of `e`.
  have hTz : ∀ k (i : Fin r) (j : Fin l), i.val < d' → l' ≤ j.val → T k i j = 0 := by
    intro k i j hi hj
    have h0 := hz i j hi hj
    rw [hPMQ] at h0
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Subfield.coe_subtype] at h0
    refine Fintype.linearIndependent_iff.mp he (fun k => T k i j) ?_ k
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  have hconj : P'.map g * NX.submatrix I id * Q'.map g = ∑ k, c k • (T k).map g := by
    rw [hNX, sub_sum]; exact conj_sum _ _ _ _ _
  have hzK : ∀ (i : Fin r) (j : Fin l), i.val < d' → l' ≤ j.val →
      (P'.map g * NX.submatrix I id * Q'.map g) i j = 0 := by
    intro i j hi hj
    rw [hconj]
    simp [Matrix.sum_apply, hTz _ i j hi hj]
  -- S2: the rank is unchanged.
  have hPg : IsUnit (P'.map g).det := by rw [det_map]; exact hPdet.map g
  have hQg : IsUnit (Q'.map g).det := by rw [det_map]; exact hQdet.map g
  have hrank : (P'.map g * NX.submatrix I id * Q'.map g).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQg, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPg,
      hrI]
  have hB2 := DiazModulus.matrix_rank_le_of_zero_block _ d' l' hzK hd'r
  rw [hrank] at hB2
  have hMIr : MI.rank ≤ M.rank := Matrix.rank_submatrix_le _ _ _
  have hl'pos : 0 < l' := by omega
  have h2 : r * l' ≤ (2 * MI.rank) * l' :=
    calc r * l' ≤ MI.rank * (d' + l') := hineq
      _ ≤ MI.rank * (2 * l') := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * MI.rank) * l' := by ring
  have h3 := le_of_mul_le_mul_right h2 hl'pos
  omega

end RC3_C22

open DiazModulus RC3_C22 in
theorem solution {d l m : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (e : Fin m → ℂ) (he : LinearIndependent (↥Qbar) e) (N : Fin m → Matrix (Fin d) (Fin l) ↥Qbar)
    (hMN : M = ∑ k, e k • (N k).map ((↑) : ↥Qbar → ℂ)) :
    (∑ k, (algebraMap (MvPolynomial (Fin m) ↥Qbar) (FractionRing (MvPolynomial (Fin m) ↥Qbar))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ↥Qbar (FractionRing (MvPolynomial (Fin m) ↥Qbar)))).rank ≤ 2 * M.rank :=
  main (algebraMap ↥Qbar (FractionRing (MvPolynomial (Fin m) ↥Qbar))) M hM e he N hMN
    (fun k => algebraMap (MvPolynomial (Fin m) ↥Qbar) (FractionRing (MvPolynomial (Fin m) ↥Qbar))
      (MvPolynomial.X k))
