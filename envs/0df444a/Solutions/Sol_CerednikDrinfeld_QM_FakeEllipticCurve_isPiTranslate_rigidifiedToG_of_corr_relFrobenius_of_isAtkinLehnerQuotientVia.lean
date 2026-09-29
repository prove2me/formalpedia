-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isPiTranslate_rigidifiedToG_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d6e5a280-8c6f-511e-8fcc-ea4658b66010

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isPiTranslate_of_isRigTransport_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isFormalModuleVia_pair
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_one_rigidifiedToG_leg_eq_frobTwist_neg_of_forall_isIdempotentElem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPiTranslate_rigidifiedToG_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd"
p2m_attr_erase "instance" "MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing"
p2m_attr_erase "simp" "CerednikDrinfeld.FormalODModule.frobTwist_F CerednikDrinfeld.FormalODModule.frobTwist_frobTwist CerednikDrinfeld.FormalODModule.frobTwist_varpi CerednikDrinfeld.FormalODModule.frobTwist_act MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.presheaf_map_apply"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace F530

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

theorem frobTwist_frobTwist {B : Type} [CommRing B] [Algebra 𝒪 B] (a b : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (frobTwist Onr Fr b ψ) = frobTwist Onr Fr (b + a) ψ := by
  apply AlgHom.ext
  intro x
  simp [frobTwist, AlgHom.comp_apply, zpow_add, AlgEquiv.mul_apply]

theorem frobTwist_zero {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr 0 ψ = ψ := by
  apply AlgHom.ext
  intro x
  simp [frobTwist]

theorem frobTwist_comm {B : Type} [CommRing B] [Algebra 𝒪 B] (a b : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (frobTwist Onr Fr b ψ) = frobTwist Onr Fr b (frobTwist Onr Fr a ψ) := by
  rw [frobTwist_frobTwist, frobTwist_frobTwist, add_comm]

theorem frobTwist_comp {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
    (a : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (φ.comp ψ) = φ.comp (frobTwist Onr Fr a ψ) := by
  apply AlgHom.ext
  intro x
  simp [frobTwist]

end F530

open F530 in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 M B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (hFV : (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
        mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
        mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q)) ∧
      (∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) ∧ (∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
        FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
        FactorsThrough A₀r.lev Q → FactorsThrough A₀.lev (mapPt V hV Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
        mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
        mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q) ∧
      (∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
        x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)) :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
      (E E' : FakeEllipticCurve Λ N B)
      (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f),
      FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq' →
      ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr 1 ψ) E'),
        (∃ (qb : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : qb ≫ ρ'.gb = ρ.gb ≫ q) (_ : qb ≫ ρ'.Eb.f = ρ.Eb.f)
          (uA : ρ'.Ab.A ⟶ A₀r.A)
          (_ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρ'.Ab uA)
          (_ : uA ≫ prA = ρ'.gA)
          (Fb : ρ.Ab.A ⟶ ρ'.Ab.A) (_ : Fb ≫ uA = ρ.gA ≫ F) (_ : Fb ≫ ρ'.Ab.f = ρ.Ab.f)
          (i j : ℕ),
          qb ≫ ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ Fb ≫ ρ'.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
        ModuliPackage.G.IsPiTranslate ι Φ η Fr (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩) := by
  classical
  have hC3a := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isPiTranslate_of_isRigTransport_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia
        (r := r) (rbar := rbar) (N := N) (hrr := hrr) (hrN := hrN) (𝒪 := 𝒪) (hdvr := hdvr) (π := π) (hπ := hπ) (hcomplete := hcomplete) (hres := hres) (hunr := hunr) (K₀ := K₀) (Onr := Onr) (Fr := Fr) (hOnr_complete := hOnr_complete) (hOnr_max := hOnr_max) (hOnr_alg := hOnr_alg) (hOnr_closed := hOnr_closed) (hFr := hFr) (a := a) (b := b) (hB := hB) (Λ := Λ) (hΛ := hΛ) (hΛℤ := hΛℤ) (coord := coord) (hcoord := hcoord) (A₀ := A₀) (X₀ := X₀) (hX₀ := hX₀) (θ₀ := θ₀) (hA₀ := hA₀) (ι := ι) (Φ := Φ) (hΦ := hΦ) (hΦ4 := hΦ4) (M := M) (hM := hM) (η := η) (hη := hη) (E₀ := E₀) (hE₀ := hE₀) (κ := κ) (hκ := hκ) (n₀ := n₀) (β₀ := β₀) (hβ₀ := hβ₀) (Ξ := Ξ) (hΞleg := hΞleg) (hΞnat := hΞnat) (hΞiso := hΞiso) (hΞdef := hΞdef) (A₀r := A₀r) (prA := prA) (hprA := hprA) (F := F) (hF := hF) (V := V) (hV := hV) (hFV := hFV)
  have hPP := CerednikDrinfeld.QM.FakeEllipticCurve.exists_le_one_rigidifiedToG_leg_eq_frobTwist_neg_of_forall_isIdempotentElem
        (r := r) (rbar := rbar) (N := N) (hrr := hrr) (hrN := hrN) (𝒪 := 𝒪) (hdvr := hdvr) (π := π) (hπ := hπ) (hcomplete := hcomplete) (hres := hres) (hunr := hunr) (K₀ := K₀) (Onr := Onr) (Fr := Fr) (hOnr_complete := hOnr_complete) (hOnr_max := hOnr_max) (hOnr_alg := hOnr_alg) (hOnr_closed := hOnr_closed) (hFr := hFr) (a := a) (b := b) (hB := hB) (Λ := Λ) (hΛ := hΛ) (hΛℤ := hΛℤ) (coord := coord) (hcoord := hcoord) (A₀ := A₀) (X₀ := X₀) (hX₀ := hX₀) (θ₀ := θ₀) (hA₀ := hA₀) (ι := ι) (Φ := Φ) (hΦ := hΦ) (hΦ4 := hΦ4) (M := M) (hM := hM) (η := η) (hη := hη) (E₀ := E₀) (hE₀ := hE₀) (κ := κ) (hκ := hκ) (n₀ := n₀) (β₀ := β₀) (hβ₀ := hβ₀) (Ξ := Ξ) (hΞleg := hΞleg) (hΞnat := hΞnat) (hΞiso := hΞiso) (hΞdef := hΞdef)
  intro B _ _ _ ψ hB hconn E E' q hq q' hq' hAL ρ ρ' hcorr

  have hBr : IsNilpotent ((r : ℕ) : B) := by
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hunr
    have hr𝒪 : ((r : ℕ) : 𝒪) = π * ((u⁻¹ : 𝒪ˣ) : 𝒪) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    have : ((r : ℕ) : B) = algebraMap 𝒪 B π * algebraMap 𝒪 B ((u⁻¹ : 𝒪ˣ) : 𝒪) := by
      rw [← map_natCast (algebraMap 𝒪 B) r, hr𝒪, map_mul]
    rw [this]
    exact Commute.isNilpotent_mul_right (Commute.all _ _) hB

  obtain ⟨nn, f, hspan, hcov⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isFormalModuleVia_pair (q := r) coord hcoord B hBr E E'

  rcases subsingleton_or_nontrivial B with hBs | hBn
  · haveI := hBs
    haveI : Subsingleton (Onr →ₐ[𝒪] B) := ⟨fun f g => AlgHom.ext fun x => Subsingleton.elim _ _⟩
    exact ⟨Subsingleton.elim _ _, 0, Fin.elim0, Subsingleton.elim _ _, fun i => Fin.elim0 i⟩
  haveI := hBn

  have hc : ∃ i : Fin nn, ¬ IsNilpotent (f i) := by
    by_contra hall
    push Not at hall
    have hle : Ideal.span (Set.range f) ≤ nilradical B := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact mem_nilradical.mpr (hall i))
    rw [hspan, top_le_iff] at hle
    have h1 : IsNilpotent (1 : B) := mem_nilradical.mp (hle ▸ Submodule.mem_top)
    obtain ⟨m, hm⟩ := h1
    exact one_ne_zero (by rwa [one_pow] at hm)
  obtain ⟨i₀, hi₀⟩ := hc
  let f₁ : Fin nn → B := fun i => if IsNilpotent (f i) then f i₀ else f i
  have hf₁ : ∀ i, ¬ IsNilpotent (f₁ i) := by
    intro i; by_cases h : IsNilpotent (f i) <;> simp [f₁, h, hi₀]
  have hf₁eq : ∀ i, f₁ i = f i₀ ∨ f₁ i = f i := by
    intro i; by_cases h : IsNilpotent (f i) <;> simp [f₁, h]
  have hspan₁ : Ideal.span (Set.range f₁) = ⊤ := by

    have hle : Ideal.span (Set.range f) ≤ Ideal.span (Set.range f₁) ⊔ nilradical B := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      by_cases h : IsNilpotent (f i)
      · exact Ideal.mem_sup_right (mem_nilradical.mpr h)
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, by simp [f₁, h]⟩)
    rw [hspan, top_le_iff] at hle
    have h1 : (1 : B) ∈ Ideal.span (Set.range f₁) ⊔ nilradical B := hle ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    have hbn : IsNilpotent b := mem_nilradical.mp hb
    have hau : IsUnit a := by
      have : a = 1 - b := by rw [← hab]; ring
      rw [this]
      exact hbn.isUnit_one_sub
    exact Ideal.eq_top_of_isUnit_mem _ ha hau

  have key : ∀ (i : Fin nn) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f₁ i) L] (hL : IsNilpotent ((r : ℕ) : L)),
      ∃ (j j' : ℕ) (t t'' : Rigidified r Φ L),
        j' = j ∧
        (algebraMap B L).comp ((Ξ B ψ hB ⟨E, ρ⟩).ψ : Onr →+* B) =
          (algebraMap B L).comp ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
        (algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B) =
          (algebraMap B L).comp ((frobTwist Onr Fr (-(j' : ℤ)) (frobTwist Onr Fr 1 ψ) : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
        t.IsAdmissible ι ((algebraMap B L).comp ((Ξ B ψ hB ⟨E, ρ⟩).ψ : Onr →+* B)) ∧
        t''.IsAdmissible ι ((algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B)) ∧
        η L ((algebraMap B L).comp ((Ξ B ψ hB ⟨E, ρ⟩).ψ : Onr →+* B)) hL t =
          M.map (ψ' := (algebraMap B L).comp ((Ξ B ψ hB ⟨E, ρ⟩).ψ : Onr →+* B)) (Ξ B ψ hB ⟨E, ρ⟩).nilp hL (algebraMap B L) rfl (Ξ B ψ hB ⟨E, ρ⟩).pt ∧
        η L ((algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B)) hL t'' =
          M.map (ψ' := (algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B)) (Ξ B ψ hB ⟨E, ρ⟩).nilp hL (algebraMap B L) rfl (Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).pt ∧
        Rigidified.IsPiTranslate ((algebraMap B L).comp ((Ξ B ψ hB ⟨E, ρ⟩).ψ : Onr →+* B)) t t'' := by
    intro i L _ _ instL hL
    haveI : Nontrivial L := by
      refine ⟨⟨algebraMap B L 1, 0, ?_⟩⟩
      intro h10
      rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (f₁ i))] at h10
      obtain ⟨⟨m, ⟨k, rfl⟩⟩, hm⟩ := h10
      exact hf₁ i ⟨k, by simpa using hm⟩
    obtain ⟨hconnL, hcoE, hcoE'⟩ : (∀ e : L, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
        (∀ (E₁ : FakeEllipticCurve Λ N L) (g : E₁.A ⟶ E.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B L) E E₁ g →
            ∃ (X : FormalODModule r L) (θ : RelativeGroupLaw.FormalCoordinates E₁.f 2), E₁.IsFormalModuleVia coord X θ) ∧
        (∀ (E₁' : FakeEllipticCurve Λ N L) (g' : E₁'.A ⟶ E'.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B L) E' E₁' g' →
            ∃ (X' : FormalODModule r L) (θ' : RelativeGroupLaw.FormalCoordinates E₁'.f 2), E₁'.IsFormalModuleVia coord X' θ') := by
      by_cases h : IsNilpotent (f i)
      · have e : f₁ i = f i₀ := by simp [f₁, h]
        haveI : IsLocalization.Away (f i₀) L := by rw [← e]; exact instL
        exact hcov i₀ L
      · have e : f₁ i = f i := by simp [f₁, h]
        haveI : IsLocalization.Away (f i) L := by rw [← e]; exact instL
        exact hcov i L
    letI instAlg : Algebra 𝒪 L := ((algebraMap B L).comp (algebraMap 𝒪 B)).toAlgebra
    haveI : IsScalarTower 𝒪 B L := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers (f₁ i)) L inferInstance
    let φ : B →ₐ[𝒪] L := IsScalarTower.toAlgHom 𝒪 B L
    have hφ : (φ : B →+* L) = algebraMap B L := rfl
    have hLπ : IsNilpotent (algebraMap 𝒪 L π) := hB.map (algebraMap B L)

    obtain ⟨EL, g, hg, h1, h2, h3, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap B L) E
    have hgv : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) E EL g := ⟨hg, h1, h2, h3⟩
    obtain ⟨ρL, hρL⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀ B L φ ψ E EL g hgv ρ
    obtain ⟨EL', g', hg', h1', h2', h3', -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap B L) E'
    have hgv' : FakeEllipticCurve.IsPullbackVia (φ : B →+* L) E' EL' g' := ⟨hg', h1', h2', h3'⟩
    obtain ⟨ρL', hρL'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀ B L φ (frobTwist Onr Fr 1 ψ) E' EL' g' hgv' ρ'

    obtain ⟨X, θ, hXθ⟩ := hcoE EL g hgv
    obtain ⟨X', θ', hXθ'⟩ := hcoE' EL' g' hgv'
    obtain ⟨j, t, hj, htX, hRT, hadm, hΞL⟩ := hΞdef L (φ.comp ψ) hLπ hconnL hL ⟨EL, ρL⟩ X θ hXθ
    obtain ⟨j', t', hj', ht'X, hRT', hadm', hΞL'⟩ := hΞdef L (φ.comp (frobTwist Onr Fr 1 ψ)) hLπ hconnL hL ⟨EL', ρL'⟩ X' θ' hXθ'

    obtain ⟨hjj, t'', hpi, hadm'', hiso⟩ := hC3a
        B ψ hB E E' q hq q' hq' hAL ρ ρ' hcorr L φ hLπ hconnL hL EL g hgv ρL hρL EL' g' hgv' ρL' hρL'
        X θ hXθ X' θ' hXθ' j hj t htX hRT hadm j' hj' t' ht'X hRT' hadm'

    have hG := (hΞnat B L φ ψ hB hLπ ⟨E, ρ⟩ ⟨EL, ρL⟩ g hgv hρL).symm.trans hΞL
    have hG' := (hΞnat B L φ (frobTwist Onr Fr 1 ψ) hB hLπ ⟨E', ρ'⟩ ⟨EL', ρL'⟩ g' hgv' hρL').symm.trans hΞL'
    have hleg : φ.comp (Ξ B ψ hB ⟨E, ρ⟩).ψ = frobTwist Onr Fr (-(j : ℤ)) (φ.comp ψ) :=
      congrArg ModuliPackage.GPoint.ψ hG
    have hleg' : φ.comp (Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ = frobTwist Onr Fr (-(j' : ℤ)) (φ.comp (frobTwist Onr Fr 1 ψ)) :=
      congrArg ModuliPackage.GPoint.ψ hG'
    have hlegR : (algebraMap B L).comp ((Ξ B ψ hB ⟨E, ρ⟩).ψ : Onr →+* B) =
        ((frobTwist Onr Fr (-(j : ℤ)) (φ.comp ψ) : Onr →ₐ[𝒪] L) : Onr →+* L) :=
      congrArg (fun f : Onr →ₐ[𝒪] L => (f : Onr →+* L)) hleg
    have hlegR' : (algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B) =
        ((frobTwist Onr Fr (-(j' : ℤ)) (φ.comp (frobTwist Onr Fr 1 ψ)) : Onr →ₐ[𝒪] L) : Onr →+* L) :=
      congrArg (fun f : Onr →ₐ[𝒪] L => (f : Onr →+* L)) hleg'

    have etaOf : ∀ (G : ModuliPackage.GPoint 𝒪 M L) (χ : Onr →ₐ[𝒪] L) (hn : IsNilpotent ((r : ℕ) : L))
        (tt : Rigidified r Φ L), G = ⟨χ, hn, η L (χ : Onr →+* L) hn tt⟩ →
        η L (G.ψ : Onr →+* L) G.nilp tt = G.pt := by
      rintro G χ hn tt rfl; rfl
    have het := etaOf _ _ _ _ hG
    have het' := etaOf _ _ _ _ hG'
    have hadm''r : t''.IsAdmissible ι ((algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B)) := by
      rw [hlegR']; exact hadm''
    have hadm'r : t'.IsAdmissible ι ((algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B)) := by
      rw [hlegR']; exact hadm'
    have hηiso : η L ((algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B)) hL t'' =
        η L ((algebraMap B L).comp ((Ξ B (frobTwist Onr Fr 1 ψ) hB ⟨E', ρ'⟩).ψ : Onr →+* B)) hL t' :=
      (hη.1 L _ hL t'' t' hadm''r hadm'r).mpr hiso
    refine ⟨j, j', t, t'', hjj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlegR, frobTwist_comp]; rfl
    · rw [hlegR', frobTwist_comp]; rfl
    · rw [hlegR]; exact hadm
    · exact hadm''r
    · exact het
    · rw [hηiso]; exact het'
    · rw [hlegR]; exact hpi
  refine ⟨?_, nn, f₁, hspan₁, ?_⟩
  ·
    obtain ⟨jB, hjB, hxψ⟩ := hPP B ψ hB hconn ⟨E, ρ⟩
    obtain ⟨jB', hjB', hx'ψ⟩ := hPP B (frobTwist Onr Fr 1 ψ) hB hconn ⟨E', ρ'⟩
    haveI : Nontrivial (Localization.Away (f₁ i₀)) := by
      refine ⟨⟨algebraMap B _ 1, 0, ?_⟩⟩
      intro h10
      rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (f₁ i₀))] at h10
      obtain ⟨⟨m, ⟨k, rfl⟩⟩, hm⟩ := h10
      exact hf₁ i₀ ⟨k, by simpa using hm⟩
    have hLr : IsNilpotent ((r : ℕ) : Localization.Away (f₁ i₀)) := by
      have := hBr.map (algebraMap B (Localization.Away (f₁ i₀))); rwa [map_natCast] at this
    obtain ⟨j, j', t, t'', hjj, hl, hl', -⟩ := key i₀ (Localization.Away (f₁ i₀)) hLr
    have hLπ : IsNilpotent (algebraMap 𝒪 (Localization.Away (f₁ i₀)) π) := by
      have := hB.map (algebraMap B (Localization.Away (f₁ i₀))); rwa [← IsScalarTower.algebraMap_apply] at this
    let φ : B →ₐ[𝒪] Localization.Away (f₁ i₀) := IsScalarTower.toAlgHom 𝒪 B _
    have toAlg : ∀ (a b : ℤ) (χ : Onr →ₐ[𝒪] B),
        (algebraMap B (Localization.Away (f₁ i₀))).comp ((frobTwist Onr Fr a χ : Onr →ₐ[𝒪] B) : Onr →+* B) =
        (algebraMap B (Localization.Away (f₁ i₀))).comp ((frobTwist Onr Fr b χ : Onr →ₐ[𝒪] B) : Onr →+* B) → a = b := by
      intro a b χ h
      have h2 : frobTwist Onr Fr a (φ.comp χ) = frobTwist Onr Fr b (φ.comp χ) := by
        apply AlgHom.coe_ringHom_injective
        rw [frobTwist_comp, frobTwist_comp]
        exact h
      exact CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial π Onr Fr hOnr_closed hFr
        (Localization.Away (f₁ i₀)) hLπ (φ.comp χ) a b h2
    rw [hxψ] at hl
    rw [hx'ψ] at hl'
    have e1 := toAlg _ _ ψ hl
    have e2 := toAlg _ _ (frobTwist Onr Fr 1 ψ) hl'
    rw [hx'ψ, hxψ, frobTwist_frobTwist, frobTwist_frobTwist]
    congr 1
    omega
  · intro i L _ _ _ hL
    obtain ⟨j, j', t, t'', -, -, -, hadm, hadm'', het, het'', hpi⟩ := key i L hL
    exact ⟨t, t'', hadm, hadm'', het, het'', hpi⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isPiTranslate_rigidifiedToG_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPiTranslate_rigidifiedToG_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia (solution)
