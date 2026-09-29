-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0d1763d0-786c-5b9f-a604-0815756b5366

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
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_and_exists_forall_map_eq_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm MvFormalGroup.CartierModule.instModulePadicInt MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite"
p2m_attr_erase "instance" "CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one CerednikDrinfeld.FormalODModule.frobTwist_F CerednikDrinfeld.FormalODModule.frobTwist_frobTwist CerednikDrinfeld.FormalODModule.frobTwist_varpi CerednikDrinfeld.FormalODModule.frobTwist_act ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq"
p2m_attr_erase "simp" "Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlueBASE

abbrev K0 (p : ℕ) [Fact p.Prime] (k : Type) [Field k] := WittVector p k ⧸ pIdeal p (WittVector p k)

theorem bij_transport {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {M : ModuliPackage.{0, 0} p (WittVector p k)}
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (hB : IsNilpotent (p : B))
    (θB : ∀ (ψ : WittVector p k →+* B), M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
    {ψ ψ' : WittVector p k →+* B} (h : ψ = ψ') (hb : Function.Bijective (θB ψ')) : Function.Bijective (θB ψ) := by
  subst h; exact hb

theorem exists_cover {B : Type} [CommRing B] {Y : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) :
    ∃ (n : ℕ) (f : Fin n → B) (V : Fin n → Y.Opens), Ideal.span (Set.range f) = ⊤ ∧ (∀ i, IsAffineOpen (V i)) ∧
      ∀ (i : Fin n) (z : PrimeSpectrum B), z ∈ PrimeSpectrum.basicOpen (f i) → y.base z ∈ V i := by
  classical
  have key : ∀ z : PrimeSpectrum B, ∃ (g : B) (V : Y.Opens), IsAffineOpen V ∧ z ∈ PrimeSpectrum.basicOpen g ∧
      ∀ w : PrimeSpectrum B, w ∈ PrimeSpectrum.basicOpen g → y.base w ∈ V := by
    intro z
    obtain ⟨V, hV, hzV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show y.base z ∈ (⊤ : Y.Opens) from trivial)
    have hopen : IsOpen (y.base ⁻¹' (V : Set Y)) := V.isOpen.preimage y.base.hom.continuous
    obtain ⟨s, ⟨g, rfl⟩, hzg, hgs⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show z ∈ y.base ⁻¹' (V : Set Y) from hzV) hopen
    exact ⟨g, V, hV, hzg, fun w hw => hgs hw⟩
  choose g V hV hzg hgV using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z : PrimeSpectrum B => ((PrimeSpectrum.basicOpen (g z) : TopologicalSpace.Opens (PrimeSpectrum B)) : Set (PrimeSpectrum B)))
    (fun z => (PrimeSpectrum.basicOpen (g z)).isOpen) (fun z _ => Set.mem_iUnion.mpr ⟨z, hzg z⟩)
  refine ⟨t.card, fun i => g (t.equivFin.symm i), fun i => V (t.equivFin.symm i), ?_, fun i => hV _,
    fun i w hw => hgV _ w hw⟩
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
  intro z _
  obtain ⟨w, hw, hzw⟩ : ∃ w ∈ t, z ∈ (PrimeSpectrum.basicOpen (g w) : Set (PrimeSpectrum B)) := by
    simpa [Set.mem_iUnion] using ht (Set.mem_univ z)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨w, hw⟩, by simpa using hzw⟩

theorem comap_mem_basicOpen {B : Type} [CommRing B] (r : B) (L : Type) [CommRing L] [Algebra B L]
    [IsLocalization.Away r L] (z : PrimeSpectrum L) :
    PrimeSpectrum.comap (algebraMap B L) z ∈ PrimeSpectrum.basicOpen r := by
  have h : PrimeSpectrum.comap (algebraMap B L) z ∈ Set.range (PrimeSpectrum.comap (algebraMap B L)) :=
    Set.mem_range_self z
  rw [PrimeSpectrum.localization_away_comap_range L r] at h
  exact h

def algHomOver (p : ℕ) [Fact p.Prime] {B L L' : Type} [CommRing B] [CommRing L] [CommRing L']
    [Algebra ℤ_[p] B] [Algebra B L] [Algebra B L'] [Algebra ℤ_[p] L] [Algebra ℤ_[p] L']
    [IsScalarTower ℤ_[p] B L] [IsScalarTower ℤ_[p] B L']
    (g : L →+* L') (hg : ∀ b : B, g (algebraMap B L b) = algebraMap B L' b) : L →ₐ[ℤ_[p]] L' :=
  { g with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply ℤ_[p] B L, hg, ← IsScalarTower.algebraMap_apply] }

@[scoped simp] theorem algHomOver_apply (p : ℕ) [Fact p.Prime] {B L L' : Type} [CommRing B] [CommRing L] [CommRing L']
    [Algebra ℤ_[p] B] [Algebra B L] [Algebra B L'] [Algebra ℤ_[p] L] [Algebra ℤ_[p] L']
    [IsScalarTower ℤ_[p] B L] [IsScalarTower ℤ_[p] B L']
    (g : L →+* L') (hg : ∀ b : B, g (algebraMap B L b) = algebraMap B L' b) (x : L) :
    algHomOver p g hg x = g x := rfl

theorem coe_algHomOver (p : ℕ) [Fact p.Prime] {B L L' : Type} [CommRing B] [CommRing L] [CommRing L']
    [Algebra ℤ_[p] B] [Algebra B L] [Algebra B L'] [Algebra ℤ_[p] L] [Algebra ℤ_[p] L']
    [IsScalarTower ℤ_[p] B L] [IsScalarTower ℤ_[p] B L']
    (g : L →+* L') (hg : ∀ b : B, g (algebraMap B L b) = algebraMap B L' b) :
    (algHomOver p g hg : L →+* L') = g := RingHom.ext fun _ => rfl

noncomputable abbrev ψ₀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (S : Type) [CommRing S] [Algebra (K0 p k) S] :
    WittVector p k →+* S :=
  (algebraMap (K0 p k) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))

theorem map_map (p : ℕ) [Fact p.Prime] {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [Algebra ℤ_[p] B] [Algebra ℤ_[p] B'] [Algebra ℤ_[p] B'']
    (f : B →ₐ[ℤ_[p]] B') (g : B' →ₐ[ℤ_[p]] B'') (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) :
    DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) g (DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) f d) =
      DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) (g.comp f) d :=
  ((CerednikDrinfeld.FormalOmega.Omega ℚ_[p] (p : ℤ_[p])).map_comp f g d).symm

theorem algHomOver_comp_toAlgHom (p : ℕ) [Fact p.Prime] {B L L' : Type} [CommRing B] [CommRing L] [CommRing L']
    [Algebra ℤ_[p] B] [Algebra B L] [Algebra B L'] [Algebra ℤ_[p] L] [Algebra ℤ_[p] L']
    [IsScalarTower ℤ_[p] B L] [IsScalarTower ℤ_[p] B L']
    (g : L →+* L') (hg : ∀ b : B, g (algebraMap B L b) = algebraMap B L' b) :
    (algHomOver p g hg).comp (IsScalarTower.toAlgHom ℤ_[p] B L) = IsScalarTower.toAlgHom ℤ_[p] B L' :=
  AlgHom.ext fun b => by simp [hg]

section Frame

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]
    {M : ModuliPackage.{0, 0} p (WittVector p k)}
    {θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
      M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B}

theorem θ_map_eq
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
      (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (θ B ψ hB x) (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    {B B' : Type} [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    {ψ : WittVector p k →+* B} {ψ' : WittVector p k →+* B'} (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (f : B →ₐ[ℤ_[p]] B') (g : B →+* B') (hfg : (f : B →+* B') = g) (hg : g.comp ψ = ψ') (x : M.obj B ψ hB) :
    θ B' ψ' hB' (M.map hB hB' g hg x) = DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) f (θ B ψ hB x) := by
  subst hfg
  exact DeligneDatum.ext' (funext fun L => hnat B B' ψ ψ' hB hB' f hg x L)

theorem surjective_of_local (hM : M.IsZariskiSheaf)
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
      (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (θ B ψ hB x) (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (INJ : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra ℤ_[p] S] (ψ : WittVector p k →+* S)
      (hS : IsNilpotent (p : S)), (p : S) = 0 → Function.Injective (θ S ψ hS))
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k))))
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
    (hloc : ∀ V : Y.Opens, IsAffineOpen V →
      ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (K0 p k) S] [Algebra ℤ_[p] S]
        (hS : IsNilpotent (p : S)) (hp : (p : S) = 0) (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) S),
        (∀ z : ↥(Spec (CommRingCat.of S)), ((eY S (ψ₀ p k S) hS hp).symm d).1.base z ∈ V) →
        ∃ x : M.obj S (ψ₀ p k S) hS, θ S (ψ₀ p k S) hS x = d)
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra (K0 p k) B] [Algebra ℤ_[p] B]
    (hB : IsNilpotent (p : B)) (hp : (p : B) = 0) :
    Function.Surjective (θ B (ψ₀ p k B) hB) := by
  intro d

  obtain ⟨n, f, V, hf, hV, hyV⟩ := exists_cover ((eY B (ψ₀ p k B) hB hp).symm d).1
  have hpL : ∀ (L : Type) [CommRing L] [Algebra B L], (p : L) = 0 := fun L _ _ => by
    simpa using congrArg (algebraMap B L) hp
  have hnL : ∀ (L : Type) [CommRing L] [Algebra B L], IsNilpotent (p : L) := fun L _ _ =>
    ⟨1, by rw [pow_one]; exact hpL L⟩

  have hψ : ∀ (L : Type) [CommRing L] [Algebra B L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] B L]
      [Algebra (K0 p k) L] [IsScalarTower (K0 p k) B L],
      ((IsScalarTower.toAlgHom ℤ_[p] B L : B →ₐ[ℤ_[p]] L) : B →+* L).comp (ψ₀ p k B) = ψ₀ p k L := by
    intro L _ _ _ _ _ _
    rw [IsScalarTower.coe_toAlgHom]
    ext a
    simp [ψ₀, ← IsScalarTower.algebraMap_apply]

  have hx : ∀ i : Fin n, ∃ x : M.obj (Localization.Away (f i)) (ψ₀ p k (Localization.Away (f i))) (hnL _),
      θ _ (ψ₀ p k _) (hnL _) x =
        DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) (IsScalarTower.toAlgHom ℤ_[p] B (Localization.Away (f i))) d := by
    intro i
    apply hloc (V i) (hV i) (Localization.Away (f i)) (hnL _) (hpL _)
    intro z
    have key := heY B (Localization.Away (f i)) (ψ₀ p k B) (ψ₀ p k _) hB (hnL _) hp (hpL _)
      (IsScalarTower.toAlgHom ℤ_[p] B _) (hψ _) ((eY B (ψ₀ p k B) hB hp).symm d)
    rw [Equiv.apply_symm_apply] at key
    rw [← key, Equiv.symm_apply_apply]
    show (Spec.map (CommRingCat.ofHom _) ≫ ((eY B (ψ₀ p k B) hB hp).symm d).1).base z ∈ V i
    rw [Scheme.Hom.comp_base, IsScalarTower.coe_toAlgHom]
    exact hyV i _ (comap_mem_basicOpen (f i) _ z)
  choose x hx using hx

  have hcomp : ∀ (L L' : Type) [CommRing L] [CommRing L'] [Algebra B L] [Algebra B L']
      [Algebra (K0 p k) L] [IsScalarTower (K0 p k) B L] [Algebra (K0 p k) L'] [IsScalarTower (K0 p k) B L']
      (g : L →+* L') (hg : ∀ b : B, g (algebraMap B L b) = algebraMap B L' b), g.comp (ψ₀ p k L) = ψ₀ p k L' := by
    intro L L' _ _ _ _ _ _ _ _ g hg
    ext a
    simp only [ψ₀, RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (K0 p k) B L, hg, ← IsScalarTower.algebraMap_apply]

  have hθ2 : ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [Algebra ℤ_[p] L]
      [IsScalarTower ℤ_[p] B L] [Algebra (K0 p k) L] [IsScalarTower (K0 p k) B L]
      (g : Localization.Away (f i) →+* L) (hg : ∀ b : B, g (algebraMap B _ b) = algebraMap B L b),
      θ L (ψ₀ p k L) (hnL L) (M.map (hnL _) (hnL L) g (hcomp _ _ g hg) (x i)) =
        DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) (IsScalarTower.toAlgHom ℤ_[p] B L) d := by
    intro i L _ _ _ _ _ _ _ g hg
    rw [θ_map_eq hnat (hnL _) (hnL L) (algHomOver p g hg) g (coe_algHomOver p g hg) (hcomp _ _ g hg) (x i), hx i,
      map_map, algHomOver_comp_toAlgHom]

  have compat : ∀ i j : Fin n,
      M.map (ψ' := ψ₀ p k (Localization.Away (f i * f j))) (hnL _) (hnL _)
          (IsLocalization.Away.awayToAwayRight (S := Localization.Away (f i)) (f i) (f j))
          (hcomp _ _ _ (IsLocalization.Away.awayToAwayRight_eq (f i) (f j))) (x i) =
        M.map (ψ' := ψ₀ p k (Localization.Away (f i * f j))) (hnL _) (hnL _)
          (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (f j)) (f j) (f i))
          (hcomp _ _ _ (IsLocalization.Away.awayToAwayLeft_eq (f j) (f i))) (x j) := by
    intro i j
    apply INJ _ (ψ₀ p k _) (hnL _) (hpL _)
    rw [hθ2 i _ _ (IsLocalization.Away.awayToAwayRight_eq (f i) (f j)),
      hθ2 j _ _ (IsLocalization.Away.awayToAwayLeft_eq (f j) (f i))]

  obtain ⟨m, hm⟩ := (hM B (ψ₀ p k B) hB n f hf (fun i => Localization.Away (f i)) (fun i => hnL _)
      (fun i j => Localization.Away (f i * f j)) (fun i j => hnL _)
      (fun i j => IsLocalization.Away.awayToAwayRight (S := Localization.Away (f i)) (f i) (f j))
      (fun i j => IsLocalization.Away.awayToAwayLeft (S := Localization.Away (f j)) (f j) (f i))
      (fun i j b => IsLocalization.Away.awayToAwayRight_eq (f i) (f j) b)
      (fun i j b => IsLocalization.Away.awayToAwayLeft_eq (f j) (f i) b)).2 x compat
  refine ⟨m, ?_⟩

  refine (CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_eq_and_exists_forall_map_eq_of_span_eq_top
      ℤ_[p] ℚ_[p] (p : ℤ_[p]) B n f hf (fun i => Localization.Away (f i)) (fun i j => Localization.Away (f i * f j))
      (fun i j => algHomOver p (IsLocalization.Away.awayToAwayRight (S := Localization.Away (f i)) (f i) (f j))
        (IsLocalization.Away.awayToAwayRight_eq (f i) (f j)))
      (fun i j => algHomOver p (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (f j)) (f j) (f i))
        (IsLocalization.Away.awayToAwayLeft_eq (f j) (f i)))
      (fun i j b => (algHomOver_apply p _ _ _).trans (IsLocalization.Away.awayToAwayRight_eq (f i) (f j) b))
      (fun i j b => (algHomOver_apply p _ _ _).trans (IsLocalization.Away.awayToAwayLeft_eq (f j) (f i) b))).1 _ _ ?_
  intro i
  rw [← θ_map_eq hnat hB (hnL _) (IsScalarTower.toAlgHom ℤ_[p] B (Localization.Away (f i))) (algebraMap B _)
    (IsScalarTower.coe_toAlgHom _ _ _) rfl m, hm i]
  exact hx i

end Frame

end GlueBASE
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero.GlueBASE"

open GlueBASE in
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
    (hB : IsNilpotent (p : B)), (p : B) = 0 → Function.Bijective (θ B ψ hB)) := by
  intro B _ _ _ ψ hB hp

  have h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi :=
    fun m hm => LinearMap.mem_ker.mpr (h0 m hm)

  have INJ := CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
    p k ι Φ hΦ hΦ4 h0 M hM η hη hcΦ rΦ hrΦ θ hθ

  obtain ⟨Y, πY, hYlft, hYsep, hYred, eY, heY⟩ :=
    CerednikDrinfeld.FormalOmega.exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing p k

  have hker : ∀ a ∈ pIdeal p (WittVector p k), ψ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [map_mul, map_natCast, hp]
  letI instK0B : Algebra (K0 p k) B := (Ideal.Quotient.lift (pIdeal p (WittVector p k)) ψ hker).toAlgebra
  have hψ : ψ = ψ₀ p k B := by
    ext a; simp [ψ₀, instK0B, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_mk]
  refine bij_transport hB (fun ψ' => θ B ψ' hB) hψ ⟨INJ B _ hB hp, ?_⟩

  haveI := hYlft; haveI := hYsep; haveI := hYred
  have S6a := CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.exists_forall_le_existsUnique_subtype_act_pow_mem_span_apply_eq_of_isAffineOpen
    p k ι Φ hΦ hΦ4 h0Φ M hM η hη hcΦ rΦ hrΦ θ hθ Y πY eY heY
  refine surjective_of_local hM hθ.2 INJ Y πY eY heY ?_ B hB hp
  intro V hV S _ _ _ _ hS hpS d hd
  obtain ⟨n₀, m₀, h⟩ := S6a V hV
  obtain ⟨x, hx, -⟩ := h n₀ m₀ le_rfl le_rfl S hS hpS d hd
  exact ⟨x.1, hx⟩

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero (solution)
