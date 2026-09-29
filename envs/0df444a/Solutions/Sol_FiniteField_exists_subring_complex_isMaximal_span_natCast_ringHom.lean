-- Prove2me | solution 1 for FiniteField.exists_subring_complex_isMaximal_span_natCast_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c9f9d623-1c47-514a-b151-020c2e65c6b4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FiniteField_exists_subring_complex_isMaximal_span_natCast_ringHom

set_option autoImplicit false

namespace FiniteFieldSubringComplex

open Polynomial

theorem eval₂_map_intCast {S T : Type*} [CommRing S] [CommRing T] (P : ℤ[X]) (c : ℤ →+* S)
    (i : S →+* T) (x : T) : (P.map c).eval₂ i x = P.eval₂ (Int.castRingHom T) x := by
  rw [eval₂_map, RingHom.ext_int (i.comp c) (Int.castRingHom T)]

end FiniteFieldSubringComplex

open Polynomial FiniteFieldSubringComplex in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [CharP k p] :
    ∃ (A : Subring ℂ) (_ : (Ideal.span ({(p : A)} : Set A)).IsMaximal),
      Nonempty (k →+* A ⧸ Ideal.span ({(p : A)} : Set A)) := by
  classical
  have hp : p.Prime := Fact.out

  letI : Algebra (ZMod p) k := ZMod.algebra k p
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) k
  have hθint : IsIntegral (ZMod p) θ := IsIntegral.of_finite (ZMod p) θ
  set Q : (ZMod p)[X] := minpoly (ZMod p) θ with hQdef
  have hQirr : Irreducible Q := minpoly.irreducible hθint
  have hQmon : Q.Monic := minpoly.monic hθint
  let ek : AdjoinRoot Q ≃ₐ[ZMod p] k :=
    (IntermediateField.adjoinRootEquivAdjoin (ZMod p) hθint).trans
      ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv)

  have hcast : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.ringHom_surjective _
  have hlifts : Q ∈ Polynomial.lifts (Int.castRingHom (ZMod p)) :=
    (Polynomial.mem_lifts Q).mpr (Polynomial.map_surjective _ hcast Q)
  obtain ⟨P, hPQ, hPdeg, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hQmon

  have hPirr : Irreducible P :=
    Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod p)) P hPmon (hPQ ▸ hQirr)

  have hdegC : (P.map (Int.castRingHom ℂ)).degree ≠ 0 := by
    rw [hPmon.degree_map, hPdeg]
    exact (minpoly.degree_pos hθint).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (P.map (Int.castRingHom ℂ)) hdegC
  have hαeval : P.eval₂ (Int.castRingHom ℂ) α = 0 := by
    have := hα.eq_zero
    rwa [eval_map] at this
  have hαaeval : Polynomial.aeval α P = 0 := by
    rw [aeval_def]
    convert hαeval
    rfl
    rfl
  have hαint : IsIntegral ℤ α := ⟨P, hPmon, hαeval⟩

  have hmin : minpoly ℤ α = P := by
    have hdvd : minpoly ℤ α ∣ P := minpoly.isIntegrallyClosed_dvd hαint hαaeval
    have hirr : Irreducible (minpoly ℤ α) := (minpoly.prime_of_isIntegrallyClosed hαint).irreducible
    exact Polynomial.eq_of_monic_of_associated (minpoly.monic hαint) hPmon (hirr.associated_of_dvd hPirr hdvd)

  let A' : Subalgebra ℤ ℂ := Algebra.adjoin ℤ ({α} : Set ℂ)
  have e₁ : AdjoinRoot P ≃ₐ[ℤ] A' := hmin ▸ minpoly.equivAdjoin hαint

  let I₀ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  haveI hI₀max : I₀.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI : Field (ℤ ⧸ I₀) := Ideal.Quotient.field I₀
  let e₀ : ℤ ⧸ I₀ ≃+* ZMod p := Int.quotientSpanNatEquivZMod p
  have hPmap : (P.map (Ideal.Quotient.mk I₀)).map (e₀ : ℤ ⧸ I₀ →+* ZMod p) = Q := by
    rw [Polynomial.map_map, RingHom.ext_int ((e₀ : ℤ ⧸ I₀ →+* ZMod p).comp (Ideal.Quotient.mk I₀))
      (Int.castRingHom (ZMod p)), hPQ]
  have hPbar : Irreducible (P.map (Ideal.Quotient.mk I₀)) := by
    have h : Irreducible (Polynomial.mapEquiv e₀ (P.map (Ideal.Quotient.mk I₀))) := by
      rw [Polynomial.mapEquiv_apply, hPmap]
      exact hQirr
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e₀)).mp h
  haveI : Fact (Irreducible (P.map (Ideal.Quotient.mk I₀))) := ⟨hPbar⟩

  have hF1 : IsField (AdjoinRoot P ⧸ I₀.map (AdjoinRoot.of P)) :=
    MulEquiv.isField (Field.toIsField (AdjoinRoot (P.map (Ideal.Quotient.mk I₀))))
      (AdjoinRoot.quotEquivQuotMap P I₀).toMulEquiv

  have hJ : Ideal.span ({(p : A')} : Set A') = (I₀.map (AdjoinRoot.of P)).map (e₁ : AdjoinRoot P →+* A') := by
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, map_natCast]
  have hF2 : IsField (A' ⧸ Ideal.span ({(p : A')} : Set A')) :=
    MulEquiv.isField hF1 (Ideal.quotientEquiv _ _ (e₁ : AdjoinRoot P ≃+* A') hJ).symm.toMulEquiv
  have hmaxA' : (Ideal.span ({(p : A')} : Set A')).IsMaximal := Ideal.Quotient.maximal_of_isField _ hF2

  let J : Ideal A' := Ideal.span ({(p : A')} : Set A')
  have hker : ∀ a ∈ I₀, Int.castRingHom (A' ⧸ J) a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk J) p,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), mul_zero]
  let i : ZMod p →+* A' ⧸ J := (Ideal.Quotient.lift I₀ (Int.castRingHom (A' ⧸ J)) hker).comp
    (e₀.symm : ZMod p →+* ℤ ⧸ I₀)
  let αA : A' := ⟨α, Algebra.subset_adjoin (Set.mem_singleton α)⟩
  have hαA : P.eval₂ (Int.castRingHom A') αA = 0 := by
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ P (Int.castRingHom A') (A'.val : A' →+* ℂ) αA
    rw [RingHom.ext_int ((A'.val : A' →+* ℂ).comp (Int.castRingHom A')) (Int.castRingHom ℂ)] at h
    show (A'.val : A' →+* ℂ) (P.eval₂ (Int.castRingHom A') αA) = ((0 : A') : ℂ)
    rw [h]
    exact hαeval
  have hroot : Q.eval₂ i (Ideal.Quotient.mk J αA) = 0 := by
    rw [← hPQ, eval₂_map_intCast,
      ← RingHom.ext_int ((Ideal.Quotient.mk J).comp (Int.castRingHom A')) (Int.castRingHom (A' ⧸ J)),
      ← Polynomial.hom_eval₂, hαA, map_zero]
  let Φ : AdjoinRoot Q →+* A' ⧸ J := AdjoinRoot.lift i (Ideal.Quotient.mk J αA) hroot
  exact ⟨A'.toSubring, hmaxA', ⟨Φ.comp (ek.symm : k →+* AdjoinRoot Q)⟩⟩

end S_FiniteField_exists_subring_complex_isMaximal_span_natCast_ringHom
end P2MW
export P2MW.S_FiniteField_exists_subring_complex_isMaximal_span_natCast_ringHom (solution)
