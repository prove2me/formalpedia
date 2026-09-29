-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_injective_range_iff_isTangentVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/244cd356-b7ce-518c-bf80-6494bc1560e3

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

noncomputable section

namespace TanExistsBody

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

section Bases

variable (k : Type) [Field k] (sk : B →+* k)

theorem toBase_comp_geomPoint (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] :
    SquareZero.toBase k V ≫ geomPoint k sk =
      Spec.map (CommRingCat.ofHom ((algebraMap k (TrivSqZeroExt k V)).comp sk)) := by
  rw [SquareZero.toBase, geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem toBase_comp_geomPoint_eq_tangentBase :
    SquareZero.toBase k k ≫ geomPoint k sk = tangentBase k sk :=
  toBase_comp_geomPoint k sk k

theorem tangentZero_eq_basePoint : tangentZero k = SquareZero.basePoint k k := rfl

theorem tangentScale_eq_specMap (c : k) :
    tangentScale k c = SquareZero.specMap k (c • (LinearMap.id : k →ₗ[k] k)) := rfl

theorem specMap_zero (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (W : Type) [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W] :
    SquareZero.specMap k (0 : V →ₗ[k] W) = SquareZero.toBase k W ≫ SquareZero.basePoint k V := by
  rw [SquareZero.specMap, SquareZero.toBase, SquareZero.basePoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  change TrivSqZeroExt.map (0 : V →ₗ[k] W) x = algebraMap k (TrivSqZeroExt k W) (TrivSqZeroExt.fstHom k k V x)
  rw [TrivSqZeroExt.algebraMap_eq_inl]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_inl]; rfl
  · rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_inl, LinearMap.zero_apply]

end Bases

section Fibre

variable (L : RelativeGroupLaw B f) (k : Type) [Field k] (sk : B →+* k)

abbrev unitPt : SchemeHomOver (geomPoint k sk) f := L.one (geomPoint k sk)

abbrev Xk (f : A ⟶ Spec (CommRingCat.of B)) (k : Type) [Field k] (sk : B →+* k) : Scheme.{0} :=
  pullback f (geomPoint k sk)

abbrev xk (f : A ⟶ Spec (CommRingCat.of B)) (k : Type) [Field k] (sk : B →+* k) :
    Xk f k sk ⟶ Spec (CommRingCat.of k) :=
  pullback.snd f (geomPoint k sk)

def pt : Spec (CommRingCat.of k) ⟶ Xk f k sk :=
  pullback.lift (unitPt L k sk).1 (𝟙 _) (by rw [(unitPt L k sk).2, Category.id_comp])

@[reassoc (attr := simp)]
theorem pt_fst : pt L k sk ≫ pullback.fst f (geomPoint k sk) = (unitPt L k sk).1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pt_snd : pt L k sk ≫ xk f k sk = 𝟙 _ :=
  pullback.lift_snd _ _ _

abbrev TP (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] : Type :=
  TangentPoints (xk f k sk) (pt L k sk) V

variable {L k sk}
variable {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
variable {W : Type} [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W]
variable {W' : Type} [AddCommGroup W'] [Module k W'] [Module kᵐᵒᵖ W'] [IsCentralScalar k W']

theorem map_map (φ : V →ₗ[k] W) (ψ : W →ₗ[k] W') (v : TP L k sk V) : (v.map φ).map ψ = v.map (ψ ∘ₗ φ) :=
  TangentPoints.ext (by rw [TangentPoints.map_coe, TangentPoints.map_coe, TangentPoints.map_coe,
    SquareZero.specMap_comp, Category.assoc])

theorem map_id' (v : TP L k sk V) : v.map (LinearMap.id : V →ₗ[k] V) = v :=
  TangentPoints.ext (by rw [TangentPoints.map_coe, SquareZero.specMap_id, Category.id_comp])

def toA (t : SquareZero.spec k V ⟶ Spec (CommRingCat.of B)) (ht : SquareZero.toBase k V ≫ geomPoint k sk = t)
    (v : TP L k sk V) : SchemeHomOver t f :=
  ⟨v.1 ≫ pullback.fst f (geomPoint k sk), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, v.2.1, ht]⟩

@[scoped simp] theorem toA_coe (t : SquareZero.spec k V ⟶ Spec (CommRingCat.of B))
    (ht : SquareZero.toBase k V ≫ geomPoint k sk = t) (v : TP L k sk V) :
    (toA t ht v).1 = v.1 ≫ pullback.fst f (geomPoint k sk) := rfl

theorem toA_injective (t : SquareZero.spec k V ⟶ Spec (CommRingCat.of B))
    (ht : SquareZero.toBase k V ≫ geomPoint k sk = t) : Function.Injective (toA (L := L) t ht) := by
  intro v v' h
  have h1 : v.1 ≫ pullback.fst f (geomPoint k sk) = v'.1 ≫ pullback.fst f (geomPoint k sk) :=
    congrArg Subtype.val h
  exact TangentPoints.ext (pullback.hom_ext h1 (by rw [v.2.1, v'.2.1]))

theorem basePoint_toA (t : SquareZero.spec k V ⟶ Spec (CommRingCat.of B))
    (ht : SquareZero.toBase k V ≫ geomPoint k sk = t) (v : TP L k sk V) :
    SquareZero.basePoint k V ≫ (toA t ht v).1 = (unitPt L k sk).1 := by
  rw [toA_coe, ← Category.assoc, v.2.2, pt_fst]

def ofA (t : SquareZero.spec k V ⟶ Spec (CommRingCat.of B)) (ht : SquareZero.toBase k V ≫ geomPoint k sk = t)
    (P : SchemeHomOver t f) (hP : SquareZero.basePoint k V ≫ P.1 = (unitPt L k sk).1) : TP L k sk V :=
  ⟨pullback.lift P.1 (SquareZero.toBase k V) (by rw [P.2, ht]),
    ⟨pullback.lift_snd _ _ _, by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hP, pt_fst]
      · rw [Category.assoc, pullback.lift_snd, SquareZero.basePoint_toBase, pt_snd]⟩⟩

@[scoped simp] theorem toA_ofA (t : SquareZero.spec k V ⟶ Spec (CommRingCat.of B))
    (ht : SquareZero.toBase k V ≫ geomPoint k sk = t)
    (P : SchemeHomOver t f) (hP : SquareZero.basePoint k V ≫ P.1 = (unitPt L k sk).1) :
    toA t ht (ofA t ht P hP) = P :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem specMap_comp_base (φ : V →ₗ[k] W)
    (tV : SquareZero.spec k V ⟶ Spec (CommRingCat.of B)) (htV : SquareZero.toBase k V ≫ geomPoint k sk = tV)
    (tW : SquareZero.spec k W ⟶ Spec (CommRingCat.of B)) (htW : SquareZero.toBase k W ≫ geomPoint k sk = tW) :
    SquareZero.specMap k φ ≫ tV = tW := by
  rw [← htV, ← htW, SquareZero.specMap_toBase_assoc]

theorem comp_toA (φ : V →ₗ[k] W)
    (tV : SquareZero.spec k V ⟶ Spec (CommRingCat.of B)) (htV : SquareZero.toBase k V ≫ geomPoint k sk = tV)
    (tW : SquareZero.spec k W ⟶ Spec (CommRingCat.of B)) (htW : SquareZero.toBase k W ≫ geomPoint k sk = tW)
    (v : TP L k sk V) :
    schemeHomOverComp (SquareZero.specMap k φ) (specMap_comp_base φ tV htV tW htW) (toA tV htV v) =
      toA tW htW (v.map φ) :=
  Subtype.ext (by rw [schemeHomOverComp_coe, toA_coe, toA_coe, TangentPoints.map_coe, Category.assoc])

theorem toA_map_zero
    (tW : SquareZero.spec k W ⟶ Spec (CommRingCat.of B)) (htW : SquareZero.toBase k W ≫ geomPoint k sk = tW)
    (v : TP L k sk V) :
    toA tW htW (v.map (0 : V →ₗ[k] W)) = L.one tW := by
  rw [← L.one_natural (geomPoint k sk) tW (SquareZero.toBase k W) htW]
  refine Subtype.ext ?_
  rw [toA_coe, TangentPoints.map_coe, schemeHomOverComp_coe, specMap_zero, Category.assoc, Category.assoc,
    ← Category.assoc (SquareZero.basePoint k V), v.2.2, pt_fst]

end Fibre

section EckmannHilton

variable {L : RelativeGroupLaw B f} {k : Type} [Field k] {sk : B →+* k}

abbrev t₂ (k : Type) [Field k] (sk : B →+* k) : SquareZero.spec k (k × k) ⟶ Spec (CommRingCat.of B) :=
  SquareZero.toBase k (k × k) ≫ geomPoint k sk

theorem sum_comp_inl :
    ((LinearMap.fst k k k + LinearMap.snd k k k) ∘ₗ LinearMap.inl k k k) = LinearMap.id :=
  LinearMap.ext fun x => by simp

theorem sum_comp_inr :
    ((LinearMap.fst k k k + LinearMap.snd k k k) ∘ₗ LinearMap.inr k k k) = LinearMap.id :=
  LinearMap.ext fun x => by simp

theorem exists_pair (t₁ : SquareZero.spec k k ⟶ Spec (CommRingCat.of B))
    (ht₁ : SquareZero.toBase k k ≫ geomPoint k sk = t₁) (P Q : TP L k sk k) :
    ∃ R : TP L k sk (k × k),
      R.map (LinearMap.fst k k k) = P ∧ R.map (LinearMap.snd k k k) = Q ∧
        toA t₁ ht₁ (R.map (LinearMap.fst k k k + LinearMap.snd k k k)) =
          L.mul t₁ (toA t₁ ht₁ P) (toA t₁ ht₁ Q) := by

  set RA : SchemeHomOver (t₂ k sk) f :=
    L.mul (t₂ k sk) (toA (t₂ k sk) rfl (P.map (LinearMap.inl k k k)))
      (toA (t₂ k sk) rfl (Q.map (LinearMap.inr k k k))) with hRA

  have hres : ∀ φ : (k × k) →ₗ[k] k,
      schemeHomOverComp (SquareZero.specMap k φ) (specMap_comp_base φ (t₂ k sk) rfl t₁ ht₁) RA =
        L.mul t₁ (toA t₁ ht₁ (P.map (φ ∘ₗ LinearMap.inl k k k)))
          (toA t₁ ht₁ (Q.map (φ ∘ₗ LinearMap.inr k k k))) := by
    intro φ
    rw [hRA, L.mul_natural (t₂ k sk) t₁ (SquareZero.specMap k φ) (specMap_comp_base φ (t₂ k sk) rfl t₁ ht₁),
      comp_toA, comp_toA, map_map, map_map]
  have hfst : schemeHomOverComp (SquareZero.specMap k (LinearMap.fst k k k))
      (specMap_comp_base _ (t₂ k sk) rfl t₁ ht₁) RA = toA t₁ ht₁ P := by
    rw [hres, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, map_id', toA_map_zero, L.mul_one]
  have hsnd : schemeHomOverComp (SquareZero.specMap k (LinearMap.snd k k k))
      (specMap_comp_base _ (t₂ k sk) rfl t₁ ht₁) RA = toA t₁ ht₁ Q := by
    rw [hres, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, map_id', toA_map_zero, L.one_mul]

  have hcen : SquareZero.basePoint k (k × k) ≫ RA.1 = (unitPt L k sk).1 := by
    have h := congrArg Subtype.val hfst
    rw [schemeHomOverComp_coe] at h
    rw [← SquareZero.basePoint_specMap k (LinearMap.fst k k k), Category.assoc, h, basePoint_toA]
  refine ⟨ofA (t₂ k sk) rfl RA hcen, ?_, ?_, ?_⟩
  · apply toA_injective t₁ ht₁
    rw [← comp_toA (LinearMap.fst k k k) (t₂ k sk) rfl t₁ ht₁, toA_ofA, hfst]
  · apply toA_injective t₁ ht₁
    rw [← comp_toA (LinearMap.snd k k k) (t₂ k sk) rfl t₁ ht₁, toA_ofA, hsnd]
  · rw [← comp_toA (LinearMap.fst k k k + LinearMap.snd k k k) (t₂ k sk) rfl t₁ ht₁, toA_ofA, hres,
      sum_comp_inl, sum_comp_inr, map_id', map_id']

end EckmannHilton

section Assembly

variable (L : RelativeGroupLaw B f) (k : Type) [Field k] (sk : B →+* k)

theorem core (W : Type) [AddCommGroup W] [Module k W] (e₁ : TP L k sk k ≃ W)
    (h_smul : ∀ (c : k) (v : TP L k sk k), e₁ (v.map (c • (LinearMap.id : k →ₗ[k] k))) = c • e₁ v)
    (h_inj : ∀ R R' : TP L k sk (k × k), R.map (LinearMap.fst k k k) = R'.map (LinearMap.fst k k k) →
      R.map (LinearMap.snd k k k) = R'.map (LinearMap.snd k k k) → R = R')
    (h_pair : ∀ w₁ w₂ : W, ∃ R : TP L k sk (k × k), e₁ (R.map (LinearMap.fst k k k)) = w₁ ∧
      e₁ (R.map (LinearMap.snd k k k)) = w₂ ∧ e₁ (R.map (LinearMap.fst k k k + LinearMap.snd k k k)) = w₁ + w₂) :
    ∃ τ : W → SchemeHomOver (tangentBase k sk) f,
      Function.Injective τ ∧
      (∀ P, P ∈ Set.range τ ↔ IsTangentVector L k sk P) ∧
      (∀ v w, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) ∧
      (∀ (c : k) (v : W), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) := by
  have hb := toBase_comp_geomPoint_eq_tangentBase k sk
  refine ⟨fun w => toA (tangentBase k sk) hb (e₁.symm w), ?_, ?_, ?_, ?_⟩
  · intro w w' h
    exact e₁.symm.injective (toA_injective (tangentBase k sk) hb h)
  · intro P
    constructor
    · rintro ⟨w, rfl⟩
      exact basePoint_toA (tangentBase k sk) hb (e₁.symm w)
    · intro hP
      refine ⟨e₁ (ofA (tangentBase k sk) hb P hP), ?_⟩
      change toA (tangentBase k sk) hb (e₁.symm (e₁ (ofA (tangentBase k sk) hb P hP))) = P
      rw [Equiv.symm_apply_apply, toA_ofA]
  · intro w₁ w₂
    obtain ⟨R, h1, h2, h3⟩ := h_pair w₁ w₂
    obtain ⟨R', h1', h2', h3'⟩ := exists_pair (tangentBase k sk) hb (e₁.symm w₁) (e₁.symm w₂)
    have g1 : R.map (LinearMap.fst k k k) = e₁.symm w₁ := by rw [← h1, Equiv.symm_apply_apply]
    have g2 : R.map (LinearMap.snd k k k) = e₁.symm w₂ := by rw [← h2, Equiv.symm_apply_apply]
    have hRR' : R' = R := h_inj R' R (h1'.trans g1.symm) (h2'.trans g2.symm)
    rw [hRR'] at h3'
    change toA (tangentBase k sk) hb (e₁.symm (w₁ + w₂)) = _
    rw [← h3, Equiv.symm_apply_apply, h3']
  · intro c w
    have hs : e₁.symm (c • w) = (e₁.symm w).map (c • (LinearMap.id : k →ₗ[k] k)) := by
      apply e₁.injective
      rw [Equiv.apply_symm_apply, h_smul, Equiv.apply_symm_apply]
    change (toA (tangentBase k sk) hb (e₁.symm (c • w))).1 = _
    rw [hs, toA_coe, TangentPoints.map_coe, Category.assoc, tangentScale_eq_specMap]
    rfl

end Assembly

end TanExistsBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector.TanExistsBody"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector.TanExistsBody"

open TanExistsBody in
theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V) (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ ∧
      (∀ P, P ∈ Set.range τ ↔ IsTangentVector L k sk P) ∧
      (∀ v w, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) ∧
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) := by
  letI alg : Algebra k ((Xk f k sk).presheaf.stalk ((pt L k sk).base (IsLocalRing.closedPoint k))) :=
    (((Xk f k sk).presheaf.germ ⊤ ((pt L k sk).base (IsLocalRing.closedPoint k)) trivial).hom.comp
      ((xk f k sk).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
  obtain ⟨γ, hγ⟩ :=
    AlgebraicGeometry.Scheme.exists_tangentPoints_equiv_linearMap_cotangentSpace (xk f k sk) (pt L k sk)
      (pt_snd L k sk)

  refine ⟨(IsLocalRing.CotangentSpace ((Xk f k sk).presheaf.stalk ((pt L k sk).base (IsLocalRing.closedPoint k)))
      →ₗ[k] k), inferInstance, inferInstance, ?_⟩
  refine core L k sk _ (γ k) ?_ ?_ ?_
  · intro c v
    rw [hγ, LinearMap.smul_comp, LinearMap.id_comp]
  · intro R R' h1 h2
    apply (γ (k × k)).injective
    have e1 : LinearMap.fst k k k ∘ₗ γ (k × k) R = LinearMap.fst k k k ∘ₗ γ (k × k) R' := by
      rw [← hγ, ← hγ, h1]
    have e2 : LinearMap.snd k k k ∘ₗ γ (k × k) R = LinearMap.snd k k k ∘ₗ γ (k × k) R' := by
      rw [← hγ, ← hγ, h2]
    refine LinearMap.ext fun y => Prod.ext ?_ ?_
    · exact congrArg (fun g : _ →ₗ[k] k => g y) e1
    · exact congrArg (fun g : _ →ₗ[k] k => g y) e2
  · intro w₁ w₂
    refine ⟨(γ (k × k)).symm (w₁.prod w₂), ?_, ?_, ?_⟩
    · rw [hγ, Equiv.apply_symm_apply, LinearMap.fst_prod]
    · rw [hγ, Equiv.apply_symm_apply, LinearMap.snd_prod]
    · rw [hγ, Equiv.apply_symm_apply, LinearMap.add_comp, LinearMap.fst_prod, LinearMap.snd_prod]

end S_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector (solution)
