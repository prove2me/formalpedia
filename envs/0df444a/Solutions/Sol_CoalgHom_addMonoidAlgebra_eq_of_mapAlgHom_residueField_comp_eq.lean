-- Prove2me | solution 1 for CoalgHom.addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/412cf0ef-7a30-52a7-917b-72612524d01f

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CoalgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

namespace CoalgUniqLocal

theorem IsIdempotentElem.eq_of_sub_mem_jacobson {S : Type*} [CommRing S] {e e' : S} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (h : e - e' ∈ Ideal.jacobson (⊥ : Ideal S)) : e = e' := by
  have h3 : (e - e') * (1 - (e - e') * (e - e')) = 0 := by
    have h1 : e * e = e := he.eq
    have h2 : e' * e' = e' := he'.eq
    linear_combination (3 * e' - e - 1) * h1 + (1 + e' - 3 * e) * h2
  have hu : IsUnit (1 - (e - e') * (e - e')) := by
    have := Ideal.mem_jacobson_bot.1 h (-(e - e'))
    rwa [mul_neg, neg_add_eq_sub] at this
  rwa [hu.mul_left_eq_zero, sub_eq_zero] at h3

theorem map_maximalIdeal_le_jacobson {R : Type*} [CommRing R] [IsLocalRing R] {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] : (maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson]
  refine le_sInf fun J hJ => ?_
  haveI : J.IsMaximal := hJ.2
  rw [Ideal.map_le_iff_le_comap]
  have hmax : (J.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
  rw [IsLocalRing.eq_maximalIdeal hmax]

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Bialgebra R B]

theorem mem_map_of_forall_apply_mem [Coalgebra.IsCocomm R B] [Module.Finite R B] [Module.Free R B] (I : Ideal R) (δ : CartierDual R B)
    (hδ : ∀ b, δ b ∈ I) : δ ∈ I.map (algebraMap R (CartierDual R B)) := by
  classical
  let bs := Module.Free.chooseBasis R B
  have hsum : (∑ i, δ (bs i) • CartierDual.ofDual R B (bs.coord i)) = δ := by
    apply (CartierDual.toDual R B).injective
    rw [map_sum]
    simp_rw [map_smul, CartierDual.toDual_ofDual]
    exact bs.sum_dual_apply_smul_coord (CartierDual.toDual R B δ)
  rw [← hsum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hδ (bs i)))

private theorem _root_.CoalgUniqLocal.sub_apply (φ ψ : CartierDual R B) (b : B) : (φ - ψ) b = φ b - ψ b := by
  rw [← CartierDual.toDual_apply (φ - ψ) b, map_sub, LinearMap.sub_apply]
  rfl

p2m_export "CoalgUniqLocal" "sub_apply"

theorem sum_single_apply {S : Type u} [CommRing S] {M : Type w} [Fintype M] [DecidableEq M] (c : M → S) (m : M) :
    (∑ m', AddMonoidAlgebra.single m' (c m') : AddMonoidAlgebra S M).coeff m = c m := by
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  simp_rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ m)]

end CoalgUniqLocal

open CoalgUniqLocal in
theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B]
    (M : Type w) [AddCommGroup M] [Finite M]
    (f f' : B →ₗc[R] AddMonoidAlgebra R M)
    (h : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).toLinearMap ∘ₗ f.toLinearMap =
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).toLinearMap ∘ₗ f'.toLinearMap) :
    f = f' := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  obtain ⟨e, he, -, -, hf⟩ :=
    CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra (S := R) (B := B) M f
  obtain ⟨e', he', -, -, hf'⟩ :=
    CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra (S := R) (B := B) M f'

  have hcoef : ∀ (m : M) (b : B), e m b - e' m b ∈ maximalIdeal R := by
    intro m b
    have hb := congrArg (fun F : B →ₗ[R] AddMonoidAlgebra (ResidueField R) M => (F b).coeff m) h
    change (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (f b)).coeff m =
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (f' b)).coeff m at hb
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_mapAlgHom, hf, hf', sum_single_apply,
      sum_single_apply] at hb
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 hb

  have hee : e = e' := by
    funext m
    refine IsIdempotentElem.eq_of_sub_mem_jacobson (he m) (he' m) (map_maximalIdeal_le_jacobson (R := R) ?_)
    exact mem_map_of_forall_apply_mem _ _ fun b => by rw [CoalgUniqLocal.sub_apply]; exact hcoef m b
  refine CoalgHom.ext fun b => ?_
  rw [hf, hf', hee]

end S_CoalgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
end P2MW
export P2MW.S_CoalgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq (solution)
