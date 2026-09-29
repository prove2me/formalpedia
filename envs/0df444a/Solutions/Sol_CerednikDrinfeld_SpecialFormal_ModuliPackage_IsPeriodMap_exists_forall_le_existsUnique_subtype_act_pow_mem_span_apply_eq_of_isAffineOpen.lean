-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f730e133-3d49-5829-9ce1-25af14760096

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_isAlgClosed_of_lieVarpi_eq_zero
import Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing
import Theorems.Thm_AlgebraicGeometry_UniversallyInjective_of_forall_isAlgClosed_points_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
import Theorems.Thm_PadicInt_ringHom_eq_ringHom_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient instTopologicallyFGOfFiniteType CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm MvFormalGroup.CartierModule.instModulePadicInt MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra"
p2m_attr_erase "instance" "CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one CerednikDrinfeld.FormalODModule.frobTwist_F CerednikDrinfeld.FormalODModule.frobTwist_frobTwist CerednikDrinfeld.FormalODModule.frobTwist_varpi CerednikDrinfeld.FormalODModule.frobTwist_act ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply"
p2m_attr_erase "simp" "CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace S6aLocalPiece

section Generic

universe u

theorem mono_of_formallyUnramified_of_universallyInjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] [UniversallyInjective f] : Mono f := by
  have h1 : IsOpenImmersion (pullback.diagonal f) := inferInstance
  have h2 : Surjective (pullback.diagonal f) := (UniversallyInjective.iff_diagonal f).mp inferInstance
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨h1, h2⟩
  exact (pullback.isIso_diagonal_iff f).mp this

theorem eq_univ_of_isClosed_of_forall_irreducibleComponents {α : Type u} [TopologicalSpace α]
    {C : Set α} (hC : IsClosed C)
    (h : ∀ Z ∈ irreducibleComponents α, ∃ z ∈ C, IsGenericPoint z Z) : C = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨z, hzC, hz⟩ := h _ (irreducibleComponent_mem_irreducibleComponents x)
  have hx : x ∈ closure ({z} : Set α) := by
    rw [hz.def]; exact mem_irreducibleComponent
  exact hC.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzC) hx

theorem isIso_of_isClosedImmersion_of_forall_irreducibleComponents {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [IsReduced Y]
    (h : ∀ Z ∈ irreducibleComponents (Y : Type u), ∃ z ∈ Set.range f.base, IsGenericPoint z Z) : IsIso f := by
  have hsurj : Surjective f := ⟨by
    rw [← Set.range_eq_univ]
    exact eq_univ_of_isClosed_of_forall_irreducibleComponents f.isClosedEmbedding.isClosed_range h⟩
  exact isIso_of_isClosedImmersion_of_surjective f

end Generic

section Base

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

local notation "k₀" => WittVector p k ⧸ pIdeal p (WittVector p k)
local notation "qk" => Ideal.Quotient.mk (pIdeal p (WittVector p k))

abbrev ψ_ (B : Type) [CommRing B] [Algebra k₀ B] : WittVector p k →+* B := (algebraMap k₀ B).comp qk

theorem natCast_p_eq_zero : ((p : ℕ) : k₀) = 0 := by
  rw [← map_natCast qk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem p_eq_zero (B : Type) [CommRing B] [Algebra k₀ B] : ((p : ℕ) : B) = 0 := by
  rw [← map_natCast (algebraMap k₀ B), natCast_p_eq_zero, map_zero]

theorem isNilpotent_p (B : Type) [CommRing B] [Algebra k₀ B] : IsNilpotent ((p : ℕ) : B) :=
  ⟨1, by rw [pow_one, p_eq_zero p k B]⟩

def cZp : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

abbrev algZp (B : Type) [CommRing B] [Algebra k₀ B] : Algebra ℤ_[p] B := ((ψ_ p k B).comp (cZp p k)).toAlgebra

theorem algebra_eq_algZp (B : Type) [CommRing B] [Algebra k₀ B] (inst : Algebra ℤ_[p] B) : inst = algZp p k B := by
  apply Algebra.algebra_ext
  intro r
  exact congrFun (congrArg DFunLike.coe
    (PadicInt.ringHom_eq_ringHom_of_isNilpotent p (isNilpotent_p p k B) (@algebraMap ℤ_[p] B _ _ inst)
      (@algebraMap ℤ_[p] B _ _ (algZp p k B)))) r

scoped instance : IsNoetherianRing (WittVector p k) := inferInstance
scoped instance instIsNoetherianRing_k₀ : IsNoetherianRing k₀ := inferInstance

scoped instance mono_specMap_qk : Mono (Spec.map (CommRingCat.ofHom qk)) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom qk)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

def algHomZp {B B' : Type} [CommRing B] [Algebra k₀ B] [CommRing B'] [Algebra k₀ B'] (g : B →ₐ[k₀] B') :
    @AlgHom ℤ_[p] B B' _ _ _ (algZp p k B) (algZp p k B') :=
  letI := algZp p k B; letI := algZp p k B'
  { toRingHom := g.toRingHom
    commutes' := fun r => by
      show g (algebraMap k₀ B (qk (cZp p k r))) = algebraMap k₀ B' (qk (cZp p k r))
      exact g.commutes _ }

variable (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k))))

abbrev WPt (B : Type) [CommRing B] [Algebra k₀ B] : Type :=
  {y : Spec (CommRingCat.of B) ⟶ Y // y ≫ πY ≫ Spec.map (CommRingCat.ofHom qk) = Spec.map (CommRingCat.ofHom (ψ_ p k B))}

theorem specOver_comp_qk (B : Type) [CommRing B] [Algebra k₀ B] :
    Scheme.specOver (𝒪 := k₀) B ≫ Spec.map (CommRingCat.ofHom qk) = Spec.map (CommRingCat.ofHom (ψ_ p k B)) := by
  rw [Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

def toNilp {B : Type} [CommRing B] [Algebra k₀ B] (y : WPt p k Y πY B) : (Scheme.nilpPoints πY).obj B :=
  ⟨y.1, (cancel_mono (Spec.map (CommRingCat.ofHom qk))).mp (by rw [Category.assoc, y.2, specOver_comp_qk])⟩

def ofNilp {B : Type} [CommRing B] [Algebra k₀ B] (y : (Scheme.nilpPoints πY).obj B) : WPt p k Y πY B :=
  ⟨y.1, by rw [← Category.assoc, y.2, specOver_comp_qk]⟩

@[scoped simp] theorem toNilp_val {B : Type} [CommRing B] [Algebra k₀ B] (y : WPt p k Y πY B) : (toNilp p k Y πY y).1 = y.1 := rfl
@[scoped simp] theorem ofNilp_val {B : Type} [CommRing B] [Algebra k₀ B] (y : (Scheme.nilpPoints πY).obj B) :
    (ofNilp p k Y πY y).1 = y.1 := rfl
@[scoped simp] theorem ofNilp_toNilp {B : Type} [CommRing B] [Algebra k₀ B] (y : WPt p k Y πY B) :
    ofNilp p k Y πY (toNilp p k Y πY y) = y := rfl
@[scoped simp] theorem toNilp_ofNilp {B : Type} [CommRing B] [Algebra k₀ B] (y : (Scheme.nilpPoints πY).obj B) :
    toNilp p k Y πY (ofNilp p k Y πY y) = y := rfl

theorem toNilp_injective {B : Type} [CommRing B] [Algebra k₀ B] : Function.Injective (toNilp p k Y πY (B := B)) :=
  fun a b h => by rw [← ofNilp_toNilp p k Y πY a, h, ofNilp_toNilp]

omit [CharP k p] [IsAlgClosed k] in

theorem exists_algebra_of_hom {Z : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of k₀)) {T : Type} [CommRing T]
    (x : Spec (CommRingCat.of T) ⟶ Z) :
    ∃ inst : Algebra k₀ T, x ≫ fZ = @Scheme.specOver k₀ _ T _ inst :=
  ⟨(Spec.preimage (x ≫ fZ)).hom.toAlgebra, by
    simp only [Scheme.specOver, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]⟩

end Base

section Frame

variable
  (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
  (ι : Zp2 p →+* WittVector p k)
  (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
  (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
  (hΦ4 : Φ.HasHeight 4)
  (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
  (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
  (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
  Rigidified p Φ B → M.obj B ψ hB)
  (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
  (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
  (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
  (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
  (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
  (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
  η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
  (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
  ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
  ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
  (hL : IsNilpotent (p : L)),
  ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
  η L ((algebraMap B L).comp ψ) hL t =
  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
  (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
  (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
    Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
  (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
  M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
  (hθ : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap p k ι Φ M η hcΦ rΦ θ)
      (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k))))
      [LocallyOfFiniteType πY] [IsSeparated πY] [IsReduced Y]
      (eY : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), (p : B) = 0 →
        ({y : Spec (CommRingCat.of B) ⟶ Y // y ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)} ≃ OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B))
      (heY : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
          (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
          (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hp : (p : B) = 0) (hp' : (p : B') = 0)
          (g : B →ₐ[ℤ_[p]] B') (hg : (g : B →+* B').comp ψ = ψ')
          (y : {y : Spec (CommRingCat.of B) ⟶ Y // y ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)}),
          eY B' ψ' hB' hp' ⟨Spec.map (CommRingCat.ofHom (g : B →+* B')) ≫ y.1, by
              rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]⟩ =
            DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) g (eY B ψ hB hp y))

local notation "k₀" => WittVector p k ⧸ pIdeal p (WittVector p k)
local notation "qk" => Ideal.Quotient.mk (pIdeal p (WittVector p k))

def Piece (n m : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra k₀ S] (hS : IsNilpotent (p : S))
    (x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS) : Prop :=
  ∃ (r : ℕ) (f : Fin r → S), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin r) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra S L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ∧ t.n = n ∧
                (∀ j : Fin 2, (t.Φbar ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) ∧
                η L ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hL t =
                  M.map (ψ' := (algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hS hL (algebraMap S L) rfl x

include hΦ hΦ4 h0Φ hM hη hrΦ hθ in

theorem exists_point_thresholds (y : Y) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k₀ K) (g : (Scheme.nilpPoints πY).obj K)
      (u : M.obj K (ψ_ p k K) (isNilpotent_p p k K)),
      y ∈ Set.range g.1.base ∧
      @θ K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K) u =
        @eY K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K) (p_eq_zero p k K) (ofNilp p k Y πY g) ∧
      ∃ n₁ m₁ : ℕ, ∀ n m : ℕ, n₁ ≤ n → m₁ ≤ m → Piece p k ι Φ M η n m K (isNilpotent_p p k K) u := by
  let K : Type := AlgebraicClosure (Y.residueField y)
  let gm : Spec (CommRingCat.of K) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y
  obtain ⟨inst, hg⟩ := exists_algebra_of_hom p k πY gm
  letI := inst
  letI : Algebra ℤ_[p] K := algZp p k K
  have hbij := CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isAlgClosed_of_lieVarpi_eq_zero
    p k ι Φ hΦ hΦ4 (fun v hv => LinearMap.mem_ker.mp (h0Φ hv)) M hM η hη hcΦ rΦ hrΦ θ hθ K (ψ_ p k K) (isNilpotent_p p k K)
  obtain ⟨u, hu⟩ := hbij.2 (eY K (ψ_ p k K) (isNilpotent_p p k K) (p_eq_zero p k K) (ofNilp p k Y πY ⟨gm, hg⟩))
  obtain ⟨n₁, m₁, hnm⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span
    p k ι Φ hΦ hΦ4 h0Φ M hM η hη K (isNilpotent_p p k K) u
  refine ⟨K, inferInstance, inferInstance, inst, ⟨gm, hg⟩, u, ?_, hu, n₁, m₁, fun n m hn hm => hnm n m hn hm⟩
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  show (Y.fromSpecResidueField y).base ((Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))).base _) = y
  exact Scheme.fromSpecResidueField_apply _ _

variable (n m : ℕ) (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k))))
  (e : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S)),
        (Scheme.nilpPoints fX).obj S ≃ {x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS // Piece p k ι Φ M η n m S hS x})
  (he : ∀ (S S' : Type) [CommRing S] [CommRing S'] [IsNoetherianRing S] [IsNoetherianRing S'] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S']
        (hS : IsNilpotent (p : S)) (hS' : IsNilpotent (p : S')) (g : S →ₐ[(WittVector p k ⧸ pIdeal p (WittVector p k))] S')
        (x : (Scheme.nilpPoints fX).obj S),
        ((e S' hS' ((Scheme.nilpPoints fX).map g x)) : M.obj S' ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S').comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS') =
          M.map hS hS' (g : S →+* S') (by rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]) (e S hS x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS))
  (mP : ℕ) (ιP : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mP + 1)) (WittVector p k ⧸ pIdeal p (WittVector p k))))
  (hιP : IsClosedImmersion ιP) (hcomp : ιP ≫ ProjSpace.π (WittVector p k ⧸ pIdeal p (WittVector p k)) mP = fX)

def τ (B : Type) [CommRing B] [Algebra k₀ B] [IsNoetherianRing B] (x : (Scheme.nilpPoints fX).obj B) :
    (Scheme.nilpPoints πY).obj B :=
  letI : Algebra ℤ_[p] B := algZp p k B
  toNilp p k Y πY ((eY B (ψ_ p k B) (isNilpotent_p p k B) (p_eq_zero p k B)).symm
    (θ B (ψ_ p k B) (isNilpotent_p p k B) (e B (isNilpotent_p p k B) x).1))

theorem τ_def (B : Type) [CommRing B] [Algebra k₀ B] [IsNoetherianRing B] (x : (Scheme.nilpPoints fX).obj B) :
    letI : Algebra ℤ_[p] B := algZp p k B
    τ p k ι Φ M η θ Y πY eY n m X fX e B x = toNilp p k Y πY ((eY B (ψ_ p k B) (isNilpotent_p p k B) (p_eq_zero p k B)).symm
      (θ B (ψ_ p k B) (isNilpotent_p p k B) (e B (isNilpotent_p p k B) x).1)) := rfl

local notation "τ!" => τ p k ι Φ M η θ Y πY eY n m X fX e

include hΦ hΦ4 h0Φ hM hη hrΦ hθ heY he hιP hcomp

theorem τ_natural (B B' : Type) [CommRing B] [Algebra k₀ B] [IsNoetherianRing B] [CommRing B'] [Algebra k₀ B']
    [IsNoetherianRing B'] (g : B →ₐ[k₀] B') (x : (Scheme.nilpPoints fX).obj B) :
    τ! B' ((Scheme.nilpPoints fX).map g x) = (Scheme.nilpPoints πY).map g (τ! B x) := by
  letI iB : Algebra ℤ_[p] B := algZp p k B
  letI iB' : Algebra ℤ_[p] B' := algZp p k B'
  let gZ : B →ₐ[ℤ_[p]] B' := algHomZp p k g
  have hg : (gZ : B →+* B').comp (ψ_ p k B) = ψ_ p k B' := by
    ext w
    exact g.commutes (qk w)
  apply Subtype.ext
  rw [Scheme.nilpPoints_map_val, τ_def, τ_def, toNilp_val, toNilp_val]
  set x₀ := (e B (isNilpotent_p p k B) x).1 with hx₀
  set y := (eY B (ψ_ p k B) (isNilpotent_p p k B) (p_eq_zero p k B)).symm
    (θ B (ψ_ p k B) (isNilpotent_p p k B) x₀) with hy
  have hy' : eY B (ψ_ p k B) (isNilpotent_p p k B) (p_eq_zero p k B) y = θ B (ψ_ p k B) (isNilpotent_p p k B) x₀ :=
    Equiv.apply_symm_apply _ _
  have h1 : (e B' (isNilpotent_p p k B') ((Scheme.nilpPoints fX).map g x)).1 =
      M.map (isNilpotent_p p k B) (isNilpotent_p p k B') (g : B →+* B')
        (by rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]) x₀ :=
    he B B' _ _ g x
  have h2 : θ B' (ψ_ p k B') (isNilpotent_p p k B') (M.map (isNilpotent_p p k B) (isNilpotent_p p k B') (g : B →+* B')
        (by rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]) x₀) =
      DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) gZ (θ B (ψ_ p k B) (isNilpotent_p p k B) x₀) := by
    have hbc := hθ.2 B B' (ψ_ p k B) (ψ_ p k B') (isNilpotent_p p k B) (isNilpotent_p p k B') gZ hg x₀
    exact DeligneDatum.ext' (funext fun L => hbc L)
  have h3 := heY B B' (ψ_ p k B) (ψ_ p k B') (isNilpotent_p p k B) (isNilpotent_p p k B') (p_eq_zero p k B)
    (p_eq_zero p k B') gZ hg y
  rw [hy'] at h3
  rw [h1, h2, ← h3, Equiv.symm_apply_apply]
  rfl

theorem existsUnique_ξ : ∃! h : X ⟶ Y, h ≫ πY = fX ∧
    ∀ (B : Type) [CommRing B] [Algebra k₀ B] [IsNoetherianRing B] (φ : (Scheme.nilpPoints fX).obj B),
      (τ! B φ).1 = φ.1 ≫ h := by
  haveI : LocallyOfFiniteType fX := by rw [← hcomp]; infer_instance
  exact Scheme.nilpPoints.existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural fX πY
    (fun B _ _ _ => τ! B)
    (fun B B' _ _ _ _ _ _ g φ => τ_natural p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp B B' g φ)

def ξ : X ⟶ Y := (existsUnique_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp).exists.choose

local notation "ξ!" => ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp

theorem ξ_comp_πY : ξ! ≫ πY = fX := (existsUnique_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp).exists.choose_spec.1

theorem τ_val (B : Type) [CommRing B] [Algebra k₀ B] [IsNoetherianRing B] (φ : (Scheme.nilpPoints fX).obj B) :
    (τ! B φ).1 = φ.1 ≫ ξ! :=
  (existsUnique_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp).exists.choose_spec.2 B φ

theorem eq_of_comp_ξ_eq {T : Type} [CommRing T] [Algebra k₀ T] [IsNoetherianRing T]
    (hinj : Function.Injective (@θ T _ _ (algZp p k T) (ψ_ p k T) (isNilpotent_p p k T)))
    (x y : (Scheme.nilpPoints fX).obj T) (h : x.1 ≫ ξ! = y.1 ≫ ξ!) : x = y := by
  have h1 : τ! T x = τ! T y := Subtype.ext (by rw [τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp T x, τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp T y, h])
  rw [τ_def, τ_def] at h1
  have h2 := (Equiv.injective _) (toNilp_injective p k Y πY h1)
  exact (e T _).injective (Subtype.ext (hinj h2))

theorem universallyInjective_ξ
    (hinjK : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k₀ K],
      Function.Injective (@θ K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K))) :
    UniversallyInjective ξ! := by
  apply UniversallyInjective.of_forall_isAlgClosed_points_eq
  intro K _ _ x y hxy
  obtain ⟨inst, hx⟩ := exists_algebra_of_hom p k fX x
  letI := inst
  have hy : y ≫ fX = Scheme.specOver K := by
    rw [← ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp, ← Category.assoc, ← hxy, Category.assoc, ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp, hx]
  exact congrArg Subtype.val (eq_of_comp_ξ_eq p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp (hinjK K) ⟨x, hx⟩ ⟨y, hy⟩ hxy)

theorem locallyOfFiniteType_ξ : LocallyOfFiniteType ξ! := by
  haveI : LocallyOfFiniteType fX := by rw [← hcomp]; infer_instance
  have : LocallyOfFiniteType (ξ! ≫ πY) := by rw [ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp]; infer_instance
  exact locallyOfFiniteType_of_comp _ πY

theorem isProper_ξ : IsProper ξ! := by
  haveI := hιP
  haveI : IsProper fX := by rw [← hcomp]; infer_instance
  have : IsProper (ξ! ≫ πY) := by rw [ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp]; infer_instance
  exact IsProper.of_comp _ πY

theorem formallyUnramified_ξ
    (hinjA : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [IsAlgClosed (IsLocalRing.ResidueField T)]
      [Algebra k₀ T], Function.Injective (@θ T _ _ (algZp p k T) (ψ_ p k T) (isNilpotent_p p k T))) :
    FormallyUnramified ξ! := by
  haveI := locallyOfFiniteType_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
  intro i
  dsimp only [Scheme.Cover.pullbackHom]
  refine @formallyUnramified_of_forall_lift_unique_of_isArtinianRing _ _ _ (pullback.snd ξ! (Y.affineCover.f i)) ?_ ?_
  · exact MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  intro T' T _ _ _ _ _ _ π hπ hsmall s m₀ hm₀ m₁ m₂ h₁ h₁' h₂ h₂'
  have h₁s : m₁ ≫ pullback.snd ξ! (Y.affineCover.f i) = s := h₁
  have h₂s : m₂ ≫ pullback.snd ξ! (Y.affineCover.f i) = s := h₂
  have e1 : ∀ w : Spec (CommRingCat.of T') ⟶ X, w ≫ fX = (w ≫ ξ!) ≫ πY := fun w => by
    rw [Category.assoc, ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp]
  apply pullback.hom_ext
  · have H : (m₁ ≫ pullback.fst ξ! (Y.affineCover.f i)) ≫ ξ! = (m₂ ≫ pullback.fst ξ! (Y.affineCover.f i)) ≫ ξ! := by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, h₁s, h₂s]
    obtain ⟨inst, hx⟩ := exists_algebra_of_hom p k fX (m₁ ≫ pullback.fst ξ! (Y.affineCover.f i))
    letI := inst
    have hy : (m₂ ≫ pullback.fst ξ! (Y.affineCover.f i)) ≫ fX = Scheme.specOver T' := by
      rw [← hx, e1, e1, H]
    exact congrArg Subtype.val (eq_of_comp_ξ_eq p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp (hinjA T') ⟨_, hx⟩ ⟨_, hy⟩ H)
  · rw [h₁s, h₂s]

theorem isClosedImmersion_ξ
    (hinjK : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k₀ K],
      Function.Injective (@θ K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K)))
    (hinjA : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [IsAlgClosed (IsLocalRing.ResidueField T)]
      [Algebra k₀ T], Function.Injective (@θ T _ _ (algZp p k T) (ψ_ p k T) (isNilpotent_p p k T))) :
    IsClosedImmersion ξ! := by
  haveI := isProper_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp
  haveI := universallyInjective_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp hinjK
  haveI := formallyUnramified_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp hinjA
  haveI : Mono ξ! := mono_of_formallyUnramified_of_universallyInjective ξ!
  exact (IsClosedImmersion.iff_isProper_and_mono ξ!).mpr ⟨inferInstance, inferInstance⟩

theorem range_subset_range_ξ {K : Type} [Field K] [IsAlgClosed K] [Algebra k₀ K] (g : (Scheme.nilpPoints πY).obj K)
    (u : M.obj K (ψ_ p k K) (isNilpotent_p p k K))
    (hu : @θ K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K) u =
      @eY K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K) (p_eq_zero p k K) (ofNilp p k Y πY g))
    (hP : Piece p k ι Φ M η n m K (isNilpotent_p p k K) u) :
    Set.range g.1.base ⊆ Set.range (ξ!).base := by
  obtain ⟨x, hx⟩ := (e K (isNilpotent_p p k K)).surjective ⟨u, hP⟩
  have h1 : τ! K x = g := by
    rw [τ_def, hx]
    change toNilp p k Y πY ((@eY K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K) (p_eq_zero p k K)).symm
      (@θ K _ _ (algZp p k K) (ψ_ p k K) (isNilpotent_p p k K) u)) = g
    rw [hu, Equiv.symm_apply_apply, toNilp_ofNilp]
  have h2 : g.1 = x.1 ≫ ξ! := by rw [← h1]; exact τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp K x
  rintro _ ⟨pt, rfl⟩
  refine ⟨x.1.base pt, ?_⟩
  rw [h2]
  rfl

end Frame

end S6aLocalPiece
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen.S6aLocalPiece"

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
(hθ : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap p k ι Φ M η hcΦ rΦ θ)
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k))))
    [LocallyOfFiniteType πY] [IsSeparated πY] [IsReduced Y]
    (eY : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), (p : B) = 0 →
      ({y : Spec (CommRingCat.of B) ⟶ Y // y ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)} ≃ OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B))
    (heY : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
        (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
        (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hp : (p : B) = 0) (hp' : (p : B') = 0)
        (g : B →ₐ[ℤ_[p]] B') (hg : (g : B →+* B').comp ψ = ψ')
        (y : {y : Spec (CommRingCat.of B) ⟶ Y // y ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)}),
        eY B' ψ' hB' hp' ⟨Spec.map (CommRingCat.ofHom (g : B →+* B')) ≫ y.1, by
            rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]⟩ =
          DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) g (eY B ψ hB hp y))
    :
    ∀ (V : Y.Opens), IsAffineOpen V → ∃ n₀ m₀ : ℕ, ∀ (n m : ℕ), n₀ ≤ n → m₀ ≤ m →
      ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] [Algebra ℤ_[p] S]
        (hS : IsNilpotent (p : S)) (hp : (p : S) = 0) (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) S),
        (∀ z : ↥(Spec (CommRingCat.of S)), ((eY S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS hp).symm d).1.base z ∈ V) →
        ∃! x : {x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS //
            ∃ (r : ℕ) (f : Fin r → S), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin r) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra S L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ∧ t.n = n ∧
                (∀ j : Fin 2, (t.Φbar ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) ∧
                η L ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hL t =
                  M.map (ψ' := (algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hS hL (algebraMap S L) rfl x},
          θ S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS x.1 = d := by
  intro V hV
  classical

  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian πY
  haveI : IsAffine (V : Scheme.{0}) := hV
  haveI : IsNoetherian (V : Scheme.{0}) := ⟨⟩
  haveI : Fintype (irreducibleComponents (V : Type)) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := (V : Type))).fintype

  let gen : irreducibleComponents (V : Type) → (V : Type) := fun Z => Z.2.1.genericPoint
  have hgen : ∀ Z : irreducibleComponents (V : Type), IsGenericPoint (gen Z) Z.1 := fun Z => by
    have := Z.2.1.isGenericPoint_genericPoint_closure
    rwa [(isClosed_of_mem_irreducibleComponents Z.1 Z.2).closure_eq] at this
  have hA := fun Z : irreducibleComponents (V : Type) =>
    S6aLocalPiece.exists_point_thresholds p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY (gen Z).1
  choose K fK aK iK g u hyr hu n₁ m₁ hP using hA
  refine ⟨Finset.univ.sup n₁, Finset.univ.sup m₁, ?_⟩
  intro n m hn hm S _ _ _ instZ hS hp d hd

  obtain rfl : instZ = S6aLocalPiece.algZp p k S := S6aLocalPiece.algebra_eq_algZp p k S instZ
  letI instZ' : Algebra ℤ_[p] S := S6aLocalPiece.algZp p k S
  obtain rfl : hS = S6aLocalPiece.isNilpotent_p p k S := rfl
  obtain rfl : hp = S6aLocalPiece.p_eq_zero p k S := rfl

  obtain ⟨X, fX, e, he, mP, ιP, hιP, hcomp⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace p k ι Φ hΦ hΦ4 h0Φ M hM η hη n m
  have HINJ := CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero p k ι Φ hΦ hΦ4 (fun v hv => LinearMap.mem_ker.mp (h0Φ hv)) M hM η hη hcΦ rΦ hrΦ θ hθ
  have hinjK : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) K],
      Function.Injective (@θ K _ _ (S6aLocalPiece.algZp p k K) (S6aLocalPiece.ψ_ p k K) (S6aLocalPiece.isNilpotent_p p k K)) :=
    fun K _ _ _ => @HINJ K _ _ (S6aLocalPiece.algZp p k K) _ _ (S6aLocalPiece.p_eq_zero p k K)
  have hinjA : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [IsAlgClosed (IsLocalRing.ResidueField T)]
      [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) T],
      Function.Injective (@θ T _ _ (S6aLocalPiece.algZp p k T) (S6aLocalPiece.ψ_ p k T) (S6aLocalPiece.isNilpotent_p p k T)) :=
    fun T _ _ _ _ _ => @HINJ T _ _ (S6aLocalPiece.algZp p k T) _ _ (S6aLocalPiece.p_eq_zero p k T)
  let ξ' : X ⟶ Y := S6aLocalPiece.ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp
  haveI hCI : IsClosedImmersion ξ' := S6aLocalPiece.isClosedImmersion_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp hinjK hinjA

  have hrange : ∀ Z : irreducibleComponents (V : Type), (gen Z).1 ∈ Set.range ξ'.base := fun Z =>
    S6aLocalPiece.range_subset_range_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp (g Z) (u Z) (hu Z)
      (hP Z n m (le_trans (Finset.le_sup (Finset.mem_univ Z)) hn) (le_trans (Finset.le_sup (Finset.mem_univ Z)) hm)) (hyr Z)

  haveI hiso : IsIso (ξ' ∣_ V) := by
    refine S6aLocalPiece.isIso_of_isClosedImmersion_of_forall_irreducibleComponents (ξ' ∣_ V) fun Z hZ => ?_
    obtain ⟨x₀, hx₀⟩ := hrange ⟨Z, hZ⟩
    have hxV : x₀ ∈ ξ' ⁻¹ᵁ V := by
      show ξ'.base x₀ ∈ (V : Set Y)
      rw [hx₀]; exact (gen ⟨Z, hZ⟩).2
    refine ⟨gen ⟨Z, hZ⟩, ⟨⟨x₀, hxV⟩, Subtype.ext ?_⟩, hgen ⟨Z, hZ⟩⟩
    rw [morphismRestrict_base_coe]; exact hx₀

  set yW := (eY S (S6aLocalPiece.ψ_ p k S) (S6aLocalPiece.isNilpotent_p p k S) (S6aLocalPiece.p_eq_zero p k S)).symm d with hyW
  have hyπ : yW.1 ≫ πY = Scheme.specOver S := (S6aLocalPiece.toNilp p k Y πY yW).2
  have hsub : Set.range yW.1.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact hd z
  let y' : Spec (CommRingCat.of S) ⟶ V := IsOpenImmersion.lift V.ι yW.1 hsub
  have hy' : y' ≫ V.ι = yW.1 := IsOpenImmersion.lift_fac _ _ _
  let z : Spec (CommRingCat.of S) ⟶ X := y' ≫ inv (ξ' ∣_ V) ≫ (ξ' ⁻¹ᵁ V).ι
  have hz : z ≫ ξ' = yW.1 := by
    simp only [z, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hy']
  have hzX : z ≫ fX = Scheme.specOver S := by
    rw [← S6aLocalPiece.ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp, ← Category.assoc]
    change (z ≫ ξ') ≫ πY = _
    rw [hz, hyπ]
  let x₀ : (Scheme.nilpPoints fX).obj S := ⟨z, hzX⟩
  have hτ₀ : S6aLocalPiece.τ p k ι Φ M η θ Y πY eY n m X fX e S x₀ = S6aLocalPiece.toNilp p k Y πY yW := by
    apply Subtype.ext
    rw [S6aLocalPiece.τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp S x₀, S6aLocalPiece.toNilp_val]
    exact hz
  rw [S6aLocalPiece.τ_def] at hτ₀
  have hθ₀ := (Equiv.injective _) (S6aLocalPiece.toNilp_injective p k Y πY hτ₀)

  refine ⟨e S _ x₀, hθ₀, ?_⟩

  intro xx hxx
  apply Subtype.ext
  exact (HINJ S (S6aLocalPiece.ψ_ p k S) (S6aLocalPiece.isNilpotent_p p k S) (S6aLocalPiece.p_eq_zero p k S)) (hxx.trans hθ₀.symm)

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen.S6aLocalPiece"

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen (solution)
