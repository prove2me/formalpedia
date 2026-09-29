-- Prove2me | solution 1 for CohCarrier.subsingleton_H2_gamma0_of_isUnit_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/568fae7f-0d67-5a1f-be2b-edbbbe9dea87

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_CohCarrier_subsingleton_H2_GammaH
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index

set_option autoImplicit false

namespace Ws23
namespace E2

open CategoryTheory groupCohomology

universe u

section CoresRes

open CategoryTheory groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]
  [DecidableRel (QuotientGroup.rightRel S)]

noncomputable def unitCoind (A : Rep.{u} k G) :
    A ⟶ (Rep.coindFunctor k S.subtype).obj ((Rep.resFunctor S.subtype).obj A) :=
  (Rep.resCoindAdjunction k S.subtype).unit.app A

noncomputable def traceHom (A : Rep.{u} k G) :
    (Rep.coindFunctor k S.subtype).obj ((Rep.resFunctor S.subtype).obj A) ⟶ A :=
  (Rep.coindResAdjunction k S).counit.app A

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem unit_trace (A : Rep.{u} k G) : unitCoind S A ≫ traceHom S A = S.index • 𝟙 A := by
  ext a
  simp only [unitCoind, traceHom, Rep.coindResAdjunction_counit_app, Adjunction.mkOfHomEquiv_unit_app,
    Rep.indResAdjunction, Adjunction.mkOfHomEquiv_counit_app]
  change ((Rep.resCoindHomEquiv S.subtype A ((Rep.resFunctor S.subtype).obj A) (𝟙 _) ≫
      (Rep.res S.subtype A).indCoindIso.inv ≫
      (Rep.indResHomEquiv S.subtype ((Rep.resFunctor S.subtype).obj A) A).symm (𝟙 _))).hom.toLinearMap a = _
  simp only [Rep.resCoindHomEquiv_apply, Rep.indResHomEquiv_symm_apply, Rep.hom_comp,
    Representation.IntertwiningMap.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply, Rep.hom_ofHom,
    Representation.IntertwiningMap.coe_toLinearMap]
  have hinv : ∀ x, (Rep.Hom.hom (Rep.res S.subtype A).indCoindIso.inv) x = (Rep.res S.subtype A).coindToInd x :=
    fun x => rfl
  have hunit : ∀ g : G, ((Rep.Hom.hom (Rep.resCoindToHom S.subtype A (Rep.of (MonoidHom.comp A.ρ S.subtype))
      (𝟙 (Rep.res S.subtype A)))) a).1 g = A.ρ g a := fun g => rfl
  simp only [hinv]
  erw [Rep.coindToInd_apply]
  rw [map_sum]
  rw [Finset.sum_congr rfl (g := fun _ => a) ?_]
  · rw [Finset.sum_const, Finset.card_univ, Rep.nsmul_hom, Rep.hom_id,
      Representation.IntertwiningMap.coe_nsmul, Pi.smul_apply, Representation.IntertwiningMap.id_apply,
      Fintype.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S), ← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card]
  · intro q _
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [Quotient.liftOn_mk, LinearMap.comp_apply, TensorProduct.mk_apply,
        Representation.Coinvariants.lift_mk, TensorProduct.lift.tmul, Finsupp.lift_apply,
        MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, Finsupp.sum_single_index, zero_smul, one_smul, hunit, Rep.hom_id, Representation.IntertwiningMap.coe_toLinearMap,
        Representation.IntertwiningMap.id_apply]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

noncomputable def shapiroIso (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology ((Rep.coindFunctor k S.subtype).obj ((Rep.resFunctor S.subtype).obj A)) n ≅
      groupCohomology ((Rep.resFunctor S.subtype).obj A) n :=
  coindIso ((Rep.resFunctor S.subtype).obj A) n

noncomputable def res' (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology ((Rep.resFunctor S.subtype).obj A) n :=
  (functor k G n).map (unitCoind S A) ≫ (shapiroIso S A n).hom

noncomputable def cores (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology ((Rep.resFunctor S.subtype).obj A) n ⟶ groupCohomology A n :=
  (shapiroIso S A n).inv ≫ (functor k G n).map (traceHom S A)

scoped instance functor_additive (n : ℕ) : (functor k G n).Additive where
  map_add {A B f g} := by
    show (cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n).map (f + g) =
      (cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n).map f +
        (cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n).map g
    exact Functor.map_add _

theorem res'_cores (A : Rep.{u} k G) (n : ℕ) :
    res' S A n ≫ cores S A n = S.index • 𝟙 (groupCohomology A n) := by
  rw [res', cores, Category.assoc]

  erw [Iso.hom_inv_id_assoc]
  show (functor k G n).map (unitCoind S A) ≫ (functor k G n).map (traceHom S A) = _
  rw [← Functor.map_comp, unit_trace, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

theorem subsingleton_of_subsingleton_res (A : Rep.{u} k G) (n : ℕ)
    [hS : Subsingleton (groupCohomology ((Rep.resFunctor S.subtype).obj A) n)]
    (hidx : IsUnit (S.index : k)) : Subsingleton (groupCohomology A n) := by
  have key : ∀ z : groupCohomology A n, (S.index : k) • z = 0 := fun z => by
    have h := congrArg (fun φ => (ModuleCat.Hom.hom φ) z) (res'_cores S A n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_nsmul, ModuleCat.hom_id,
      LinearMap.smul_apply, LinearMap.id_apply] at h
    rw [Subsingleton.elim ((ModuleCat.Hom.hom (res' S A n)) z) 0, map_zero] at h
    rw [Nat.cast_smul_eq_nsmul, ← h]
  have hz : ∀ z : groupCohomology A n, z = 0 := fun z =>
    (hidx.smul_left_cancel).1 (by rw [key z, smul_zero])
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end CoresRes

section Transport

variable {k G G' : Type u} [CommRing k] [Group G] [Group G']

theorem subsingleton_H2_of_mulEquiv (e : G ≃* G') (B : Rep k G)
    (h : Subsingleton (H2 (Rep.of (B.ρ.comp e.symm.toMonoidHom)))) : Subsingleton (H2 B) := by
  refine ⟨fun x y => ?_⟩
  induction x using H2_induction_on with
  | h x =>
    induction y using H2_induction_on with
    | h y =>
      apply (H2π_eq_iff x y).2

      have hf' : (fun p : G' × G' => ((x - y : cocycles₂ B) : G × G → B) (e.symm p.1, e.symm p.2)) ∈
          cocycles₂ (Rep.of (B.ρ.comp e.symm.toMonoidHom)) := by
        rw [mem_cocycles₂_iff]
        intro g h' j
        have hc := (mem_cocycles₂_iff ((x - y : cocycles₂ B) : G × G → B)).1 (x - y).2
          (e.symm g) (e.symm h') (e.symm j)
        simp only [map_mul] at hc ⊢
        exact hc
      have h0 : H2π (Rep.of (B.ρ.comp e.symm.toMonoidHom)) ⟨_, hf'⟩ =
          H2π (Rep.of (B.ρ.comp e.symm.toMonoidHom)) 0 := Subsingleton.elim _ _
      rw [H2π_eq_iff] at h0
      obtain ⟨x', hx'⟩ := h0
      refine ⟨fun g => x' (e g), funext fun gh => ?_⟩
      obtain ⟨g, h'⟩ := gh
      have key := congrFun hx' (e g, e h')
      rw [d₁₂_hom_apply] at key
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.symm_apply_apply] at key

      have key2 : (B.ρ g) (x' (e h')) - x' (e g * e h') + x' (e g) =
          ((x - y : cocycles₂ B) : G × G → B) (e.symm (e g), e.symm (e h')) - 0 := key
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, sub_zero, ← map_mul] at key2
      rw [d₁₂_hom_apply]
      exact key2

end Transport

section Level

open scoped MatrixGroups
open CongruenceSubgroup

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem Gamma_le_GammaH : Gamma M ≤ CohCarrier.GammaH M H := by
  intro γ hγ
  obtain ⟨ha, hb, hc, hd⟩ := Gamma_mem.mp hγ
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨Gamma0_mem.mpr hc, ?_⟩
  have : CohCarrier.gamma0Units M ⟨γ, Gamma0_mem.mpr hc⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    exact hd
  rw [this]
  exact one_mem H

scoped instance GammaH_finiteIndex [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  (show IsCongruenceSubgroup (CohCarrier.GammaH M H) from ⟨M, NeZero.ne M, Gamma_le_GammaH M H⟩).finiteIndex

theorem index_subgroupOf_gamma0_eq [NeZero M] :
    ((CohCarrier.GammaH M H).subgroupOf (Gamma0 M)).index = H.index := by
  have h1 : ((CohCarrier.GammaH M H).subgroupOf (Gamma0 M)).index * (Gamma0 M).index =
      (CohCarrier.GammaH M H).index :=
    Subgroup.relIndex_mul_index (CohCarrier.GammaH_le_Gamma0 H)
  rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index M H, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) h1

end Level

open scoped MatrixGroups in
open CongruenceSubgroup in
theorem main {k : Type} [CommRing k] (M r : ℕ) [NeZero M] (hrM : r ∣ M) (hr : 4 ≤ r)
    (H : Subgroup (ZMod M)ˣ) (hH : ∀ u ∈ H, ZMod.castHom hrM (ZMod r) (u : ZMod M) = 1)
    (hunit : IsUnit ((H.index : ℕ) : k))
    (A : Rep k ↥(Gamma0 M)) : Subsingleton (groupCohomology A 2) := by
  classical
  set S : Subgroup ↥(Gamma0 M) := (CohCarrier.GammaH M H).subgroupOf (Gamma0 M) with hS

  haveI : Subsingleton (groupCohomology ((Rep.resFunctor S.subtype).obj A) 2) := by
    let e : ↥S ≃* ↥(CohCarrier.GammaH M H) := Subgroup.subgroupOfEquivOfLe (CohCarrier.GammaH_le_Gamma0 H)
    exact subsingleton_H2_of_mulEquiv e ((Rep.resFunctor S.subtype).obj A)
      (CohCarrier.subsingleton_H2_GammaH M r hrM hr H hH _)
  refine subsingleton_of_subsingleton_res S A 2 ?_
  rw [hS, index_subgroupOf_gamma0_eq]
  exact hunit

end Ws23.E2
p2m_reactivate "P2MW.S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index.Ws23 P2MW.S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index.Ws23.E2"
p2m_reactivate "P2MW.S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index.Ws23"

theorem solution
    {k : Type} [CommRing k] (M r : ℕ) [NeZero M] (hrM : r ∣ M) (hr : 4 ≤ r)
    (H : Subgroup (ZMod M)ˣ) (hH : ∀ u ∈ H, ZMod.castHom hrM (ZMod r) (u : ZMod M) = 1)
    (hunit : IsUnit ((H.index : ℕ) : k))
    (A : Rep k ↥(CongruenceSubgroup.Gamma0 M)) : Subsingleton (groupCohomology A 2) :=
  Ws23.E2.main M r hrM hr H hH hunit A

end S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index
end P2MW
export P2MW.S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index (solution)
