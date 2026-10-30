-- Prove2me | solution 1 for DiazModulus.exists_isWeaklyRegular_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T18:19:22.73249+00:00
-- url     : https://prove2.me/submissions/57e88ed5-ebf5-453f-a57c-e9d01f1eb7d8

import Mathlib

open RingTheory.Sequence Pointwise

/-! # The linear forms `X_i - a_i` are a weakly regular sequence in `R[X_σ]`

Ring isomorphisms carry weakly regular sequences (`AddEquiv.isWeaklyRegular_congr`). The one-variable
step: if `rs` is weakly regular on `R`, then `X - b` followed by the constants `C(rs)` is weakly regular
on `R[X]`, because `X - b` is monic, hence a nonzerodivisor, and `R[X]/(X - b) ≅ R` as an `R`-module
(`Polynomial.quotientSpanXSubCAlgEquiv`), so that the rest of the sequence is `rs` itself
(`isWeaklyRegular_map_algebraMap_iff`). Induction on `n` through
`R[X_0, …, X_n] ≅ R[X_1, …, X_n][X]` (`MvPolynomial.finSuccEquiv`, which sends `X` to `X_0` and the
constants `X_j` to `X_{j+1}`) shows that `(X_i - a_i)_{i < n}` is weakly regular on
`R[X_0, …, X_{n-1}]`. For a finite `σ`, renaming along `σ ≃ Fin #σ` (`MvPolynomial.renameEquiv`) gives
a weakly regular sequence of length `#σ` in `R[X_σ]`, each entry of which vanishes at `a`. -/

namespace C12_RV

/-- A ring isomorphism carries weakly regular sequences to weakly regular sequences. -/
lemma isWeaklyRegular_map_ringEquiv {S S' : Type*} [CommRing S] [CommRing S'] (φ : S ≃+* S')
    {rs : List S} (h : IsWeaklyRegular S rs) : IsWeaklyRegular S' (rs.map φ) :=
  (AddEquiv.isWeaklyRegular_congr (e := φ.toAddEquiv) (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun r _ x => map_mul φ r x))).mp h

/-- `X - b` followed by the constants of a weakly regular sequence of `R` is weakly regular on
`R[X]`. -/
lemma polynomial_isWeaklyRegular_cons {R : Type*} [CommRing R] (b : R) {rs : List R}
    (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular (Polynomial R) ((Polynomial.X - Polynomial.C b) :: rs.map Polynomial.C) := by
  rw [isWeaklyRegular_cons_iff]
  refine ⟨(Polynomial.monic_X_sub_C b).isRegular.left, ?_⟩
  have hI : (Polynomial.X - Polynomial.C b) • (⊤ : Submodule (Polynomial R) (Polynomial R)) =
      Ideal.span {Polynomial.X - Polynomial.C b} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop (Polynomial.X - Polynomial.C b) (Polynomial R) ≃ₗ[R] R :=
    ((Submodule.quotEquivOfEq _ _ hI).restrictScalars R).trans
      (Polynomial.quotientSpanXSubCAlgEquiv b).toLinearEquiv
  have h' : IsWeaklyRegular (QuotSMulTop (Polynomial.X - Polynomial.C b) (Polynomial R)) rs :=
    (e.isWeaklyRegular_congr rs).mpr h
  exact (isWeaklyRegular_map_algebraMap_iff (Polynomial R) _ rs).mpr h'

open MvPolynomial in
/-- `(X_i - a_i)_{i < n}` is weakly regular on `R[X_0, …, X_{n-1}]`. -/
lemma mvPolynomial_fin_isWeaklyRegular {R : Type*} [CommRing R] :
    ∀ (n : ℕ) (a : Fin n → R),
      IsWeaklyRegular (MvPolynomial (Fin n) R) (List.ofFn fun i => X i - C (a i))
  | 0, _ => by simp
  | n + 1, a => by
    have ih := mvPolynomial_fin_isWeaklyRegular n (fun i => a i.succ)
    have hP := polynomial_isWeaklyRegular_cons (C (a 0)) ih
    have hφ := isWeaklyRegular_map_ringEquiv (finSuccEquiv R n).symm.toRingEquiv hP
    have h0 : (finSuccEquiv R n).symm Polynomial.X = X 0 := by
      rw [AlgEquiv.symm_apply_eq, finSuccEquiv_X_zero]
    have hs : ∀ j : Fin n, (finSuccEquiv R n).symm (Polynomial.C (X j)) = X j.succ := by
      intro j; rw [AlgEquiv.symm_apply_eq, finSuccEquiv_X_succ]
    have hc : ∀ r : R, (finSuccEquiv R n).symm (Polynomial.C (C r)) = C r := by
      intro r
      have := (finSuccEquiv R n).symm.commutes r
      simpa [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] using this
    have hl : List.map (finSuccEquiv R n).symm.toRingEquiv ((Polynomial.X - Polynomial.C (C (a 0)))
        :: List.map Polynomial.C (List.ofFn fun i => X i - C (a i.succ))) =
        List.ofFn fun i : Fin (n + 1) => X i - C (a i) := by
      rw [List.ofFn_succ, List.map_cons, List.map_map, List.map_ofFn]
      simp [h0, hc, hs, Function.comp_def]
    rw [hl] at hφ
    exact hφ

end C12_RV

open C12_RV MvPolynomial in
theorem solution {σ R : Type*} [CommRing R] [Finite σ] (a : σ → R) :
    ∃ zs : List (MvPolynomial σ R), zs.length = Nat.card σ ∧ (∀ z ∈ zs, MvPolynomial.eval a z = 0) ∧
      RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ R) zs := by
  let e := Finite.equivFin σ
  have h := isWeaklyRegular_map_ringEquiv (renameEquiv R e.symm).toRingEquiv
    (mvPolynomial_fin_isWeaklyRegular _ (fun i => a (e.symm i)))
  refine ⟨_, by simp, ?_, h⟩
  simp
