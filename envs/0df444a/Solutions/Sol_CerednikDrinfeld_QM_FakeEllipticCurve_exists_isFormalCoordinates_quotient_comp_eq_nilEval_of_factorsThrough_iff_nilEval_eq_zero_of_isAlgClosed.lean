-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/66729345-0f4c-5ccb-ae22-b58f9f0a7891

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_span_range_germ_eq_span_range_of_mapPt_eq_one_iff_of_factorsThrough_iff_nilEval_eq_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
import Theorems.Thm_MvFormalGroup_exists_isLawHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree_of_isComm
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem Q2_assemble_aux
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k]
    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)
    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f') (act' : ↥Λ → (A' ⟶ A'))
    (hact' : ∀ x : ↥Λ, act' x ≫ f' = f')
    (hact'_mul : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      pushPt (act' x) (hact' x) (L'.mul t P Q) = L'.mul t (pushPt (act' x) (hact' x) P) (pushPt (act' x) (hact' x) Q))
    (p : A.A ⟶ A') (hp : p ≫ f' = A.f) (hp_act : ∀ x : ↥Λ, A.act x ≫ p = p ≫ act' x)
    (θ'' : RelativeGroupLaw.FormalCoordinates f' 2) (T : Series k)
    (hpT : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ p = (θ'' B'' (fun i => MvFormalGroup.nilEval m (T i) s)).1)
    (u : Series k) (huγ : u.comp γ = T)
    (θ' : RelativeGroupLaw.FormalCoordinates f' 2) (hθ' : L'.IsFormalCoordinates Y.F θ')
    (hθ'eq : ∀ (C : Type) [CommRing C] [Algebra k C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → C, (∀ i, s i ∈ J) → θ' C s = θ'' C (fun i => MvFormalGroup.nilEval n (u i) s)) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates f' 2,
      L'.IsFormalCoordinates Y.F θ' ∧
      (∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
          θ' B' (fun i => MvFormalGroup.nilEval m
              (Series.addVia Y.F (Y.act (coord x).1) ((Y.act (coord x).2).comp Y.varpi) i) s) =
            pushPt (act' x) (hact' x) (θ' B' s)) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ p = (θ' B'' (fun i => MvFormalGroup.nilEval m (γ i) s)).1) := by
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := hγ.1.1.1
  have hgerm : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ p = (θ' B'' (fun i => MvFormalGroup.nilEval m (γ i) s)).1 := by
    intro B'' _ _ J m hJ s hs
    have hγJ : ∀ j, MvFormalGroup.nilEval m (γ j) s ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs γ hγ0 (u 0)).1
    rw [hpT B'' J m hJ s hs, hθ'eq B'' J m hJ _ hγJ]
    have hXY : (fun i => MvFormalGroup.nilEval m (T i) s) =
        (fun i => MvFormalGroup.nilEval m (u i) (fun j => MvFormalGroup.nilEval m (γ j) s)) := by
      funext i
      have hTi : T i = MvPowerSeries.subst γ (u i) := by rw [← huγ]; rfl
      rw [hTi]
      exact (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs γ hγ0 (u i)).2
    rw [hXY]
  refine ⟨θ', hθ', ?_, hgerm⟩
  exact CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
    coord hcoord k A XA θA hA Y γ hγ.1 hγ.2 L' act' hact' hact'_mul p hp hp_act θ' hθ' hgerm

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))

    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA) (hA4 : XA.HasHeight 4)

    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h)

    (K : Scheme.{0}) (ι : K ⟶ A.A) (hι_closed : IsClosedImmersion ι)
    (hι_finite : IsFinite (ι ≫ A.f)) (hι_flat : Flat (ι ≫ A.f)) (hι_fp : LocallyOfFinitePresentation (ι ≫ A.f))
    (hι_rank : ∀ y : ↥(Spec (CommRingCat.of k)), (ι ≫ A.f).finrank y = r ^ h)
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (A.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (A.L.mul t P Q) ∧ FactorsThrough ι (A.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough ι P → FactorsThrough ι (pushPt (A.act x) (A.act_over x) P))
    (c : ℕ)
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough ι P → nsmulPt A.L t (r ^ c) P = A.L.one t)
    (hKγ : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (FactorsThrough ι (θA B'' s) ↔ ∀ i, MvFormalGroup.nilEval n (γ i) s = 0))

    (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f') (act' : ↥Λ → (A' ⟶ A'))
    (hact' : ∀ x : ↥Λ, act' x ≫ f' = f')
    (p : A.A ⟶ A') (hp : p ≫ f' = A.f) (ψ : A' ⟶ A.A) (hψ : ψ ≫ A.f = f')
    (hL'_comm : L'.IsCommutative)
    (hA'_bundle : AbelianSchemePropertyBundle k f')
    (hA'_dim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f'.base ⁻¹' {s}) = 2)
    (hact'_mul : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      pushPt (act' x) (hact' x) (L'.mul t P Q) = L'.mul t (pushPt (act' x) (hact' x) P) (pushPt (act' x) (hact' x) Q))

    (hp_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      mapPt p hp (A.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q))
    (hp_act : ∀ x : ↥Λ, A.act x ≫ p = p ≫ act' x)
    (hp_finite : IsFinite p) (hp_flat : Flat p) (hp_fp : LocallyOfFinitePresentation p) (hp_surj : Surjective p)
    (hp_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      mapPt p hp P = L'.one t ↔ FactorsThrough ι P)

    (hψ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      mapPt ψ hψ (L'.mul t P Q) = A.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψ_act : ∀ x : ↥Λ, act' x ≫ ψ = ψ ≫ A.act x)
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      mapPt ψ hψ (mapPt p hp P) = nsmulPt A.L t (r ^ c) P)
    (hpψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f'),
      mapPt p hp (mapPt ψ hψ Q) = nsmulPt L' t (r ^ c) Q)

    (hp_univ : ∀ (X : Scheme.{0}) (gX : X ⟶ Spec (CommRingCat.of k)) (LX : RelativeGroupLaw k gX) (φ : A.A ⟶ X) (hφ : φ ≫ gX = A.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
        mapPt φ hφ (A.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
        FactorsThrough ι P → mapPt φ hφ P = LX.one t) →
      ∃! χ : SchemeHomOver f' gX, p ≫ χ.1 = φ ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t f'),
          mapPt χ.1 χ.2 (L'.mul t u v) = LX.mul t (mapPt χ.1 χ.2 u) (mapPt χ.1 χ.2 v)) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates f' 2,

      L'.IsFormalCoordinates Y.F θ' ∧
      (∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
          θ' B' (fun i => MvFormalGroup.nilEval m
              (Series.addVia Y.F (Y.act (coord x).1) ((Y.act (coord x).2).comp Y.varpi) i) s) =
            pushPt (act' x) (hact' x) (θ' B' s)) ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ p = (θ' B'' (fun i => MvFormalGroup.nilEval m (γ i) s)).1) := by
  classical

  obtain ⟨F', θ'', T, hF'c, hθ'', hT, hpT⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field
      k A.L XA.F θA hA.1 L' hL'_comm hA'_bundle hA'_dim p hp hp_mul

  have hI : Ideal.span (Set.range T) = Ideal.span (Set.range γ) :=
    GoodReductionJacobian.RelativeGroupLaw.span_range_germ_eq_span_range_of_mapPt_eq_one_iff_of_factorsThrough_iff_nilEval_eq_zero
      k A.L XA.F θA hA.1 L' F' θ'' hθ'' p hp T hT hpT γ hγ.1.1.1 K ι hp_ker hKγ

  haveI : XA.F.IsComm := XA.isComm
  haveI : Y.F.IsComm := Y.isComm
  haveI : F'.IsComm := hF'c
  obtain ⟨u, v, hu, hv, hvu, huv, huγ, hvT⟩ :=
    MvFormalGroup.exists_isLawHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree_of_isComm
      XA.F Y.F F' γ T hγ.1.1 hT hγ.2 hI.symm

  have hΨΦ : hv.toHom.comp hu.toHom = MvFormalGroup.Hom.id Y.F := by
    apply MvFormalGroup.Hom.ext
    funext i
    exact congrFun hvu i
  have hΦΨ : hu.toHom.comp hv.toHom = MvFormalGroup.Hom.id F' := by
    apply MvFormalGroup.Hom.ext
    funext i
    exact congrFun huv i
  obtain ⟨hθ', hθ'eq⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFormalCoordinates_comp_adicEval_of_hom L' F' Y.F θ'' hθ''
      hu.toHom hv.toHom hΨΦ hΦΨ
  exact Q2_assemble_aux coord hcoord k A XA θA hA Y γ h hγ L' act' hact' hact'_mul p hp hp_act θ'' T hpT u huγ
    _ hθ' hθ'eq

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed (solution)
