-- Prove2me | solution 1 for F3SubsetSum.corollary_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T21:23:41.019097+00:00
-- url     : https://prove2.me/submissions/aff9f27f-2fd6-4006-90c0-4c5fcdf2cb46

import Definitions.Def_F3SubsetSum_QuotientAlgebra
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Set.Card

open MvPolynomial F3SubsetSum

/- The quotient by the field equations is the algebra of all functions on the finite grid.
Imposing the sample equations restricts those functions to the candidate set. We prove this
evaluation isomorphism directly, then read off its dimension and its values on 1 and X j. -/

section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

private lemma field_product (j : Fin n) :
    (∏ a : K, (X j - C a : MvPolynomial (Fin n) K)) =
      X j ^ Fintype.card K - X j := by
  classical
  have hc : (1 : ℕ) < Fintype.card K := Fintype.one_lt_card
  have hp : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub (by simpa using hc)
  have hr : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).roots.card =
      (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X]
    simp [FiniteField.X_pow_card_sub_X_natDegree_eq K hc]
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hr
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  have he := congrArg (Polynomial.aeval (X j : MvPolynomial (Fin n) K)) h
  simpa using he

-- Alon's grid Nullstellensatz identifies polynomials vanishing on the full grid.
private lemma vanishes_grid_mem (I : Ideal (MvPolynomial (Fin n) K))
    (hI : ∀ j, X j ^ Fintype.card K - X j ∈ I)
    (p : MvPolynomial (Fin n) K) (hp : ∀ u : Fin n → K, eval u p = 0) : p ∈ I := by
  classical
  obtain ⟨h, _, heq⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ : Fin n => (Finset.univ : Finset K)) (fun _ => Finset.univ_nonempty) p (fun u _ => hp u)
  rw [heq, Finsupp.linearCombination_apply]
  apply I.sum_mem
  intro j _
  change h j * (∏ a : K, (X j - C a)) ∈ I
  rw [field_product]
  exact I.mul_mem_left _ (hI j)

end

section
variable {q n m : ℕ} [Fact q.Prime]
variable (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q)

omit [Fact q.Prime] in
private lemma sample_mem (i : Fin m) : fPoly A b i ∈ idealJ A b :=
  Ideal.subset_span (Or.inl ⟨i, rfl⟩)

private lemma eval_zero_of_mem {u : Fin n → ZMod q} (hu : u ∈ candidates A b)
    {p : MvPolynomial (Fin n) (ZMod q)} (hp : p ∈ idealJ A b) : eval u p = 0 := by
  have h : idealJ A b ≤ RingHom.ker (eval u) := by
    apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact hu i
    · simp [RingHom.mem_ker, ZMod.pow_card]
  exact h hp

private lemma grid_vanish_mem {p : MvPolynomial (Fin n) (ZMod q)}
    (hp : ∀ u, eval u p = 0) : p ∈ idealJ A b := by
  apply vanishes_grid_mem (idealJ A b) _ p hp
  intro j
  rw [ZMod.card]
  exact Ideal.subset_span (Or.inr ⟨j, rfl⟩)

private lemma interpolation_mem (p : MvPolynomial (Fin n) (ZMod q)) :
    p - ∑ u : Fin n → ZMod q, C (eval u p) * indicator u ∈ idealJ A b := by
  classical
  apply grid_vanish_mem A b
  intro u
  simp only [map_sub, map_sum, map_mul, eval_C]
  rw [Finset.sum_eq_single u]
  · simp [eval_indicator_apply_eq_one]
  · intro v _ hv
    rw [eval_indicator_apply_eq_zero u v hv.symm, mul_zero]
  · simp

-- An indicator outside the candidate set is killed by one sample equation.
private lemma indicator_mem_of_not_candidate (u : Fin n → ZMod q)
    (hu : u ∉ candidates A b) : indicator u ∈ idealJ A b := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, eval u (fPoly A b i) ≠ 0 := by
    simpa only [candidates, Set.mem_ofPred_eq, not_forall] using hu
  let c := eval u (fPoly A b i)
  have h : C c * indicator u - fPoly A b i * indicator u ∈ idealJ A b := by
    apply grid_vanish_mem A b
    intro v
    by_cases hv : v = u
    · subst v
      simp [c]
    · simp [eval_indicator_apply_eq_zero v u hv]
  have hprod : C c * indicator u ∈ idealJ A b :=
    by simpa only [sub_add_cancel] using
      (idealJ A b).add_mem h ((idealJ A b).mul_mem_right (indicator u) (sample_mem A b i))
  have hc : c ≠ 0 := hi
  have hscaled := (idealJ A b).mul_mem_left (C c⁻¹) hprod
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hscaled

-- Interpolation now identifies J with the kernel of evaluation on candidates.
private lemma mem_ideal_iff (p : MvPolynomial (Fin n) (ZMod q)) :
    p ∈ idealJ A b ↔ ∀ u ∈ candidates A b, eval u p = 0 := by
  classical
  constructor
  · exact fun hp u hu => eval_zero_of_mem A b hu hp
  · intro hp
    have hsum : (∑ u : Fin n → ZMod q, C (eval u p) * indicator u) ∈ idealJ A b := by
      apply (idealJ A b).sum_mem
      intro u _
      by_cases hu : u ∈ candidates A b
      · simp [hp u hu]
      · exact (idealJ A b).mul_mem_left _ (indicator_mem_of_not_candidate A b u hu)
    have h := (idealJ A b).add_mem (interpolation_mem A b p) hsum
    simpa only [sub_add_cancel] using h

private noncomputable def candidateEval :
    MvPolynomial (Fin n) (ZMod q) →ₐ[ZMod q] (candidates A b → ZMod q) :=
  AlgHom.pi fun u : candidates A b => aeval u.val

private lemma candidateEval_apply (p : MvPolynomial (Fin n) (ZMod q)) (u : candidates A b) :
    candidateEval A b p u = eval u.val p := rfl

private lemma candidateEval_surjective : Function.Surjective (candidateEval A b) := by
  classical
  intro f
  refine ⟨∑ u : candidates A b, C (f u) * indicator u.val, ?_⟩
  ext v
  simp only [candidateEval_apply, map_sum, map_mul, eval_C]
  rw [Finset.sum_eq_single v]
  · simp [eval_indicator_apply_eq_one]
  · intro u _ hu
    have hv : v.val ≠ u.val := fun h => hu (Subtype.ext h.symm)
    rw [eval_indicator_apply_eq_zero _ _ hv, mul_zero]
  · simp

private noncomputable def quotientEval :
    (MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b) →ₐ[ZMod q]
      (candidates A b → ZMod q) :=
  Ideal.Quotient.liftₐ _ (candidateEval A b) (by
    intro p hp
    ext u
    exact eval_zero_of_mem A b u.property hp)

private lemma quotientEval_apply (p : MvPolynomial (Fin n) (ZMod q)) (u : candidates A b) :
    quotientEval A b (Ideal.Quotient.mk _ p) u = eval u.val p := rfl

private lemma quotientEval_bijective : Function.Bijective (quotientEval A b) := by
  constructor
  · apply (injective_iff_map_eq_zero (quotientEval A b)).mpr
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (mem_ideal_iff A b p).mpr
    intro u hu
    exact congrFun hx ⟨u, hu⟩
  · intro f
    obtain ⟨p, hp⟩ := candidateEval_surjective A b f
    exact ⟨Ideal.Quotient.mk _ p, hp⟩

-- This is the evaluation isomorphism in Claim 4.1 of the paper.
private noncomputable def quotientEquiv :
    (MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b) ≃ₐ[ZMod q]
      (candidates A b → ZMod q) :=
  AlgEquiv.ofBijective (quotientEval A b) (quotientEval_bijective A b)

private lemma dimension_eq_candidate_count :
    Module.finrank (ZMod q) (MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b) =
      (candidates A b).ncard := by
  classical
  calc
    _ = Module.finrank (ZMod q) (candidates A b → ZMod q) :=
      (quotientEquiv A b).toLinearEquiv.finrank_eq
    _ = Fintype.card (candidates A b) := Module.finrank_fintype_fun_eq_card _
    _ = _ := Set.fintypeCard_eq_ncard _

private lemma singleton_conclusions (s : Fin n → ZMod q) (h : candidates A b = {s}) :
    Ideal.Quotient.mk (idealJ A b) 1 ≠ 0 ∧
      Submodule.span (ZMod q) {Ideal.Quotient.mk (idealJ A b) 1} = ⊤ ∧
      ∀ j : Fin n, Ideal.Quotient.mk (idealJ A b) (X j) =
        s j • Ideal.Quotient.mk (idealJ A b) 1 := by
  classical
  have hs : s ∈ candidates A b := by rw [h]; exact Set.mem_singleton s
  let u : candidates A b := ⟨s, hs⟩
  have hv (v : candidates A b) : v.val = s := by
    have hh := v.property
    simp only [h, Set.mem_singleton_iff] at hh
    exact hh
  have hsame (v : candidates A b) : v = u := Subtype.ext (hv v)
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have he := congrArg (fun x => quotientEval A b x u) hz
    simp only [map_one, map_zero, Pi.zero_apply, Pi.one_apply, one_ne_zero] at he
  · apply top_unique
    intro y _
    have hrepr : y = (quotientEval A b y u) • Ideal.Quotient.mk (idealJ A b) 1 := by
      apply (quotientEval_bijective A b).injective
      ext v
      simp only [map_smul, map_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      rw [hsame v]
    rw [hrepr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro j
    apply (quotientEval_bijective A b).injective
    ext v
    simp only [quotientEval_apply, eval_X, map_smul, map_one,
      Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [hv v]
end

theorem solution (q : ℕ) [Fact q.Prime] (_hq : 3 ≤ q) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    ((∃ s, candidates A b = {s}) ↔
        Module.finrank (ZMod q) (MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b) = 1) ∧
      ∀ s : Fin n → ZMod q, candidates A b = {s} →
        Ideal.Quotient.mk (idealJ A b) 1 ≠ 0 ∧
        Submodule.span (ZMod q) {Ideal.Quotient.mk (idealJ A b) 1} = ⊤ ∧
        ∀ j : Fin n, Ideal.Quotient.mk (idealJ A b) (X j) =
          s j • Ideal.Quotient.mk (idealJ A b) 1 := by
  constructor
  · rw [dimension_eq_candidate_count A b, Set.ncard_eq_one]
  · exact singleton_conclusions A b
