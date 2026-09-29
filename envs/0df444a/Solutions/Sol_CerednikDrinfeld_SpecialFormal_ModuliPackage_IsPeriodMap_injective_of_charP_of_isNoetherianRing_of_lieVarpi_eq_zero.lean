-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/05ef6f12-d176-5cb6-a3e3-d702610cf6cb

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
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_isAlgClosed_of_lieVarpi_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq
import Theorems.Thm_AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
import Theorems.Thm_PadicInt_ringHom_eq_ringHom_of_isNilpotent
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
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

namespace InjK0

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

def eK : k ≃+* k₀ := Classical.choice (WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k)

theorem isField_k₀ : IsField k₀ := (eK p k).symm.toMulEquiv.isField (Field.toIsField k)

theorem isMaximal_pIdeal : (pIdeal p (WittVector p k)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_k₀ p k)

@[reducible] def fieldK₀ : Field k₀ := @Ideal.Quotient.field _ _ (pIdeal p (WittVector p k)) (isMaximal_pIdeal p k)

theorem isAlgClosed_k₀ : @IsAlgClosed k₀ (fieldK₀ p k) := by
  letI : Field k₀ := fieldK₀ p k
  exact IsAlgClosed.of_ringEquiv k k₀ (eK p k)

example : (fieldK₀ p k).toCommRing = Ideal.Quotient.commRing (pIdeal p (WittVector p k)) := rfl

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

theorem locallyOfFiniteType_ξ : LocallyOfFiniteType ξ! := by
  haveI : LocallyOfFiniteType fX := by rw [← hcomp]; infer_instance
  have : LocallyOfFiniteType (ξ! ≫ πY) := by rw [ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp]; infer_instance
  exact locallyOfFiniteType_of_comp _ πY

theorem isProper_ξ : IsProper ξ! := by
  haveI := hιP
  haveI : IsProper fX := by rw [← hcomp]; infer_instance
  have : IsProper (ξ! ≫ πY) := by rw [ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp]; infer_instance
  exact IsProper.of_comp _ πY

theorem injective_θ_dualNumber :
    letI : Field k₀ := fieldK₀ p k
    Function.Injective (@θ (DualNumber k₀) _ inferInstance (algZp p k (DualNumber k₀)) (ψ_ p k (DualNumber k₀))
      (isNilpotent_p p k (DualNumber k₀))) := by
  letI instF : Field k₀ := fieldK₀ p k
  haveI : IsAlgClosed k₀ := isAlgClosed_k₀ p k
  letI instZκ : Algebra ℤ_[p] k₀ := algZp p k k₀

  have hinst : (inferInstance : Algebra ℤ_[p] (DualNumber k₀)) = algZp p k (DualNumber k₀) :=
    algebra_eq_algZp p k (DualNumber k₀) _
  rw [← hinst]

  let fst : DualNumber k₀ →ₐ[ℤ_[p]] k₀ := (TrivSqZeroExt.fstHom k₀ k₀ k₀).restrictScalars ℤ_[p]
  have hres : (fst : DualNumber k₀ →+* k₀).comp (ψ_ p k (DualNumber k₀)) = ψ_ p k k₀ := by
    ext w
    show TrivSqZeroExt.fst (algebraMap k₀ (DualNumber k₀) (qk w)) = algebraMap k₀ k₀ (qk w)
    rfl
  intro y y' hyy

  set d := θ (DualNumber k₀) (ψ_ p k (DualNumber k₀)) (isNilpotent_p p k (DualNumber k₀)) y with hd
  set x := M.map (isNilpotent_p p k (DualNumber k₀)) (isNilpotent_p p k k₀) (fst : DualNumber k₀ →+* k₀) hres y with hx
  set x' := M.map (isNilpotent_p p k (DualNumber k₀)) (isNilpotent_p p k k₀) (fst : DualNumber k₀ →+* k₀) hres y' with hx'
  have hbc := hθ.2 (DualNumber k₀) k₀ (ψ_ p k (DualNumber k₀)) (ψ_ p k k₀) (isNilpotent_p p k (DualNumber k₀))
    (isNilpotent_p p k k₀) fst hres y
  have hbc' := hθ.2 (DualNumber k₀) k₀ (ψ_ p k (DualNumber k₀)) (ψ_ p k k₀) (isNilpotent_p p k (DualNumber k₀))
    (isNilpotent_p p k k₀) fst hres y'

  have hθx : θ k₀ (ψ_ p k k₀) (isNilpotent_p p k k₀) x = θ k₀ (ψ_ p k k₀) (isNilpotent_p p k k₀) x' := by
    apply DeligneDatum.ext'
    funext L
    rw [hbc L, hbc' L, ← hd, hyy]
  have hinjκ := (CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isAlgClosed_of_lieVarpi_eq_zero
    p k ι Φ hΦ hΦ4 (fun v hv => LinearMap.mem_ker.mp (h0Φ hv)) M hM η hη hcΦ rΦ hrΦ θ hθ k₀ (ψ_ p k k₀) (isNilpotent_p p k k₀)).1
  have hxx : x = x' := hinjκ hθx
  exact CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero
    p k ι Φ hΦ hΦ4 (fun v hv => LinearMap.mem_ker.mp (h0Φ hv)) M hM η hη hcΦ rΦ hrΦ θ hθ k₀ (ψ_ p k k₀) (isNilpotent_p p k k₀)
    (ψ_ p k (DualNumber k₀)) (isNilpotent_p p k (DualNumber k₀)) hres x d hbc y y' rfl rfl hxx.symm hyy.symm

theorem hinj_dualNumber :
    ∀ P Q : Spec (CommRingCat.of (DualNumber k₀)) ⟶ X,
      P ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap k₀ (DualNumber k₀))) →
      Q ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap k₀ (DualNumber k₀))) →
      P ≫ ξ! = Q ≫ ξ! → P = Q := by
  intro P Q hP hQ hPQ
  letI instF : Field k₀ := fieldK₀ p k
  haveI : IsNoetherianRing (DualNumber k₀) := inferInstance
  let xP : (Scheme.nilpPoints fX).obj (DualNumber k₀) := ⟨P, hP⟩
  let xQ : (Scheme.nilpPoints fX).obj (DualNumber k₀) := ⟨Q, hQ⟩
  suffices h : xP = xQ from congrArg Subtype.val h
  have h1 : τ! (DualNumber k₀) xP = τ! (DualNumber k₀) xQ :=
    Subtype.ext (by rw [τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp _ xP, τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp _ xQ]; exact hPQ)
  rw [τ_def, τ_def] at h1
  have h2 := (Equiv.injective _) (toNilp_injective p k Y πY h1)
  have h3 := injective_θ_dualNumber p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp h2
  exact (e (DualNumber k₀) _).injective (Subtype.ext h3)

theorem isClosedImmersion_ξ : IsClosedImmersion ξ! := by
  letI : Field k₀ := fieldK₀ p k
  haveI : IsAlgClosed k₀ := isAlgClosed_k₀ p k
  haveI : IsProper fX := by haveI := hιP; rw [← hcomp]; infer_instance
  exact AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq k₀ fX πY ξ!
    (ξ_comp_πY p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp)
    (hinj_dualNumber p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp)

theorem mono_ξ : Mono ξ! := by
  haveI := isClosedImmersion_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp
  infer_instance

theorem eq_of_comp_ξ_eq {T : Type} [CommRing T] [Algebra k₀ T] [IsNoetherianRing T]
    (x y : (Scheme.nilpPoints fX).obj T) (h : x.1 ≫ ξ! = y.1 ≫ ξ!) : x = y := by
  haveI := mono_ξ p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp
  exact Subtype.ext ((cancel_mono ξ!).mp h)

theorem eq_of_piece_of_apply_eq (B : Type) [CommRing B] [Algebra k₀ B] [IsNoetherianRing B]
    (x x' : M.obj B (ψ_ p k B) (isNilpotent_p p k B))
    (hx : Piece p k ι Φ M η n m B (isNilpotent_p p k B) x) (hx' : Piece p k ι Φ M η n m B (isNilpotent_p p k B) x')
    (h : @θ B _ _ (algZp p k B) (ψ_ p k B) (isNilpotent_p p k B) x = @θ B _ _ (algZp p k B) (ψ_ p k B) (isNilpotent_p p k B) x') :
    x = x' := by

  obtain ⟨a, ha⟩ := (e B (isNilpotent_p p k B)).surjective ⟨x, hx⟩
  obtain ⟨a', ha'⟩ := (e B (isNilpotent_p p k B)).surjective ⟨x', hx'⟩
  have hτ : τ! B a = τ! B a' := by
    rw [τ_def, τ_def, ha, ha']
    change toNilp p k Y πY ((@eY B _ _ (algZp p k B) (ψ_ p k B) (isNilpotent_p p k B) (p_eq_zero p k B)).symm
        (@θ B _ _ (algZp p k B) (ψ_ p k B) (isNilpotent_p p k B) x)) =
      toNilp p k Y πY ((@eY B _ _ (algZp p k B) (ψ_ p k B) (isNilpotent_p p k B) (p_eq_zero p k B)).symm
        (@θ B _ _ (algZp p k B) (ψ_ p k B) (isNilpotent_p p k B) x'))
    rw [h]
  have hξ : a.1 ≫ ξ! = a'.1 ≫ ξ! := by
    rw [← τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp B a, ← τ_val p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp B a', hτ]
  have haa : a = a' := eq_of_comp_ξ_eq p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY n m X fX e he mP ιP hιP hcomp a a' hξ
  rw [haa] at ha
  exact congrArg Subtype.val (ha.symm.trans ha')

end Frame

end InjK0
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero.InjK0"

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
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
    :
    (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
      (hB : IsNilpotent (p : B)), (p : B) = 0 → Function.Injective (θ B ψ hB)) := by
  intro B _ _ instZ ψ hB hp
  classical

  have hψp : ∀ a ∈ pIdeal p (WittVector p k), ψ a = 0 := fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_natCast, hp, mul_zero]
  letI instK : Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) B :=
    (Ideal.Quotient.lift (pIdeal p (WittVector p k)) ψ hψp).toAlgebra
  have hψ : InjK0.ψ_ p k B = ψ :=
    RingHom.ext fun w => Ideal.Quotient.lift_mk (pIdeal p (WittVector p k)) ψ hψp

  suffices H : ∀ (instZ' : Algebra ℤ_[p] B) (ψ' : WittVector p k →+* B) (hB' : IsNilpotent (p : B)),
      instZ' = InjK0.algZp p k B → ψ' = InjK0.ψ_ p k B → Function.Injective (@θ B _ _ instZ' ψ' hB') from
    H instZ ψ hB (InjK0.algebra_eq_algZp p k B instZ) hψ.symm
  intro instZ' ψ' hB' h1 h2
  subst h1 h2
  have h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi :=
    fun v hv => LinearMap.mem_ker.mpr (h0 v hv)

  obtain ⟨Y, πY, hlft, hsep, hred, eY, heY⟩ :=
    CerednikDrinfeld.FormalOmega.exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing p k
  haveI := hlft; haveI := hsep; haveI := hred
  intro x x' hxx'

  obtain ⟨n₀, m₀, hx⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span
    p k ι Φ hΦ hΦ4 h0Φ M hM η hη B (InjK0.isNilpotent_p p k B) x
  obtain ⟨n₀', m₀', hx'⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span
    p k ι Φ hΦ hΦ4 h0Φ M hM η hη B (InjK0.isNilpotent_p p k B) x'
  have hxP : InjK0.Piece p k ι Φ M η (max n₀ n₀') (max m₀ m₀') B (InjK0.isNilpotent_p p k B) x :=
    hx _ _ (le_max_left _ _) (le_max_left _ _)
  have hx'P : InjK0.Piece p k ι Φ M η (max n₀ n₀') (max m₀ m₀') B (InjK0.isNilpotent_p p k B) x' :=
    hx' _ _ (le_max_right _ _) (le_max_right _ _)

  obtain ⟨X, fX, e, he, mP, ιP, hιP, hcomp⟩ :=
    CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace
      p k ι Φ hΦ hΦ4 h0Φ M hM η hη (max n₀ n₀') (max m₀ m₀')
  exact InjK0.eq_of_piece_of_apply_eq p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY (max n₀ n₀') (max m₀ m₀')
    X fX e he mP ιP hιP hcomp B x x' hxP hx'P hxx'

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero.InjK0"

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero (solution)
