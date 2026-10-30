-- Prove2me | solution 1 for DiazModulus.isWeaklyRegular_torusList
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:09:32.596997+00:00
-- url     : https://prove2.me/submissions/f5af81a2-4c5e-4fb5-8ee4-c079d9aac57a

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # The torus generators form a weakly regular sequence

Write `f_i = Y_i Z_i − 1`. By the definition of `IsWeaklyRegular` it suffices that, for every `j`
and every set `s` of indices with `j ∉ s`, `f_j` is a non-zero-divisor modulo `I = (f_i)_{i ∈ s}`
(the list `Finset.univ.toList` has no duplicates, so its `i`-th entry is not among the first `i`).
Split the variables into `{Y_j, Z_j}` and the rest: `rename` along `Equiv.sumCompl` and
`MvPolynomial.sumRingEquiv` give `e : R ≃+* S[Y_j, Z_j]` with `S` the polynomials in the other
variables. Then `e(f_i) ∈ C(S)` for `i ∈ s`, so `e(I) = C(I₀)·S[Y_j,Z_j]` with `I₀ = C⁻¹(e(I))`, and
by `MvPolynomial.ker_map` this is the kernel of reduction to `(S/I₀)[Y_j, Z_j]`. There `e(f_j)`
becomes `Y_j Z_j − 1`, whose constant coefficient `−1` is a unit, so it is a unit in the power
series ring (`MvPowerSeries.isUnit_iff_constantCoeff`) and hence a non-zero-divisor of the
polynomial ring (`MvPolynomial.coe_injective`). So `f_j g ∈ I ⇒ g ∈ I`. -/

namespace C11_T5
open DiazModulus MvPolynomial

theorem eq_zero_of_mul {τ Q : Type*} [CommRing Q] (P G : MvPolynomial τ Q)
    (hP : IsUnit (constantCoeff P)) (h : P * G = 0) : G = 0 := by
  have hu : IsUnit (P : MvPowerSeries τ Q) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPolynomial.coeff_coe, ← MvPolynomial.constantCoeff_eq]
    exact hP
  apply MvPolynomial.coe_injective
  have : (P : MvPowerSeries τ Q) * G = 0 := by
    rw [← MvPolynomial.coe_mul, h, MvPolynomial.coe_zero]
  rw [MvPolynomial.coe_zero]
  exact hu.mul_right_eq_zero.1 this

variable {K A₀ A₁ : Type*} [Field K]

/-- The torus generator `Y_i Z_i − 1`. -/
noncomputable abbrev tg (K A₀ : Type*) [Field K] (i : A₁) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K :=
  X (Sum.inr (i, true)) * X (Sum.inr (i, false)) - 1

theorem key [DecidableEq A₁] (j : A₁) (s : Set A₁) (hj : j ∉ s)
    (g : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
    (h : tg K A₀ j * g ∈ Ideal.span (tg K A₀ '' s)) : g ∈ Ideal.span (tg K A₀ '' s) := by
  classical
  set p : A₀ ⊕ (A₁ × Bool) → Prop := fun v => Sum.elim (fun _ => False) (fun q => q.1 = j) v
  set e := (renameEquiv K (Equiv.sumCompl p).symm).toRingEquiv.trans
    (sumRingEquiv K {v // p v} {v // ¬ p v})
  have eX_pos : ∀ v (hv : p v), e (X v) = X ⟨v, hv⟩ := by
    intro v hv
    simp [e, Equiv.sumCompl_symm_apply_of_pos hv, sumRingEquiv_X_inl]
  have eX_neg : ∀ v (hv : ¬ p v), e (X v) = C (X ⟨v, hv⟩) := by
    intro v hv
    simp [e, Equiv.sumCompl_symm_apply_of_neg hv, sumRingEquiv_X_inr]
  have hC : ∀ i ∈ s, ∃ t, e (tg K A₀ i) = C t := by
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    have h1 : ¬ p (Sum.inr (i, true)) := by simpa [p] using hij
    have h2 : ¬ p (Sum.inr (i, false)) := by simpa [p] using hij
    exact ⟨X ⟨_, h1⟩ * X ⟨_, h2⟩ - 1, by simp [tg, map_sub, map_mul, eX_neg _ h1, eX_neg _ h2]⟩
  set I := Ideal.span (tg K A₀ '' s)
  set J := I.map e
  set I₀ := J.comap (C : MvPolynomial {v // ¬ p v} K →+* _)
  have hJ : J = I₀.map C := by
    apply le_antisymm _ Ideal.map_comap_le
    show Ideal.map e (Ideal.span _) ≤ _
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    obtain ⟨t, ht⟩ := hC i hi
    rw [ht]
    refine Ideal.mem_map_of_mem C ?_
    show C t ∈ J
    rw [← ht]
    exact Ideal.mem_map_of_mem e (Ideal.subset_span ⟨i, hi, rfl⟩)
  have hker : J = RingHom.ker (map (Ideal.Quotient.mk I₀) :
      MvPolynomial {v // p v} (MvPolynomial {v // ¬ p v} K) →+* _) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ]
  have hmem : e (tg K A₀ j) * e g ∈ J := by
    rw [← map_mul]; exact Ideal.mem_map_of_mem e h
  rw [hker, RingHom.mem_ker, map_mul] at hmem
  have hy : p (Sum.inr (j, true)) := by simp [p]
  have hz : p (Sum.inr (j, false)) := by simp [p]
  have hunit : IsUnit (constantCoeff (map (Ideal.Quotient.mk I₀) (e (tg K A₀ j)))) := by
    simp [tg, map_sub, map_mul, eX_pos _ hy, eX_pos _ hz]
    exact isUnit_neg_one (α := MvPolynomial {v // ¬ p v} K ⧸ I₀)
  have hg := eq_zero_of_mul _ _ hunit hmem
  rw [← RingHom.mem_ker, ← hker] at hg
  obtain ⟨x, hx, hxg⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).1 hg
  rwa [← e.injective hxg]

end C11_T5

open DiazModulus C11_T5 in
theorem solution {K A₀ A₁ : Type*} [Field K] [Fintype A₁] :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (torusList K A₀ A₁) := by
  classical
  set L := (Finset.univ : Finset A₁).toList
  have hL : torusList K A₀ A₁ = L.map (tg K A₀) := rfl
  have hnd : L.Nodup := Finset.nodup_toList _
  constructor
  intro i hi
  have hi' : i < L.length := by simpa [hL] using hi
  have htake : Ideal.ofList ((torusList K A₀ A₁).take i) =
      Ideal.span (tg K A₀ '' {k | k ∈ L.take i}) := by
    rw [hL, ← List.map_take, Ideal.ofList]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, List.mem_map]
  have hget : (torusList K A₀ A₁)[i] = tg K A₀ L[i] := by simp [hL]
  have hnot : L[i] ∉ {k | k ∈ L.take i} := by
    intro hm
    obtain ⟨k, hk, hkL⟩ := List.mem_take_iff_getElem.1 hm
    have := (hnd.getElem_inj_iff (hi := by omega) (hj := hi')).1 hkL
    omega
  rw [hget, htake, smul_eq_mul, Ideal.mul_top]
  intro a b hab
  induction a using Submodule.Quotient.induction_on with | _ a => ?_
  induction b using Submodule.Quotient.induction_on with | _ b => ?_
  dsimp only at hab
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab
  rw [Submodule.Quotient.eq]
  apply key _ _ hnot
  rw [mul_sub]
  exact hab
