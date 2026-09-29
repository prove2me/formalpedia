-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/74acb51b-1739-5b79-8d55-ba22b82e38ef

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
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_WittVector_exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_ringHom_and_sq_eq_of_isAlgClosed
import Theorems.Thm_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two_of_charP
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_awayToLoc_tangent_eq_sum_of_iso
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_isIsomorphic_of_line_transport_of_not_node
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace QuadRigidity

p2m_open "CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule~NMod"
open CerednikDrinfeld.FormalOmega
open scoped PadicInt Padic
open scoped TensorProduct
open MvPowerSeries (constantCoeff constantCoeff_X)

variable {q : ℕ} [Fact q.Prime]

section homs

variable {A : Type} [CommRing A] {A' : Type} [CommRing A']

theorem cc_map {φ : Series A} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : A →+* A') (i : Fin 2) :
    constantCoeff ((φ.map f) i) = 0 := by
  show constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ i, map_zero]

theorem cc_id (i : Fin 2) : constantCoeff (Series.id A i) = 0 := constantCoeff_X _

variable {X Y Z : FormalODModule q A}

theorem hom_cc (f : X.Hom Y) (i : Fin 2) : constantCoeff (f.toSeries i) = 0 :=
  f.isODHom.constantCoeff i

@[scoped simp] theorem comp_toSeries (g : Y.Hom Z) (f : X.Hom Y) :
    (g.comp f).toSeries = g.toSeries.comp f.toSeries := rfl

@[scoped simp] theorem map_toSeries (r : A →+* A') (f : X.Hom Y) :
    (f.map r).toSeries = f.toSeries.map r := rfl

@[scoped simp] theorem id_toSeries : (FormalODModule.Hom.id X).toSeries = Series.id A := rfl

theorem id_isIso (X : FormalODModule q A) : (FormalODModule.Hom.id X).IsIso :=
  ⟨FormalODModule.Hom.id X, FormalODModule.Hom.ext (Series.comp_id _),
    FormalODModule.Hom.ext (Series.comp_id _)⟩

def castHom {X X' : FormalODModule q A} (h : X = X') {Y : FormalODModule q A} (w : X.Hom Y) :
    X'.Hom Y :=
  ⟨w.toSeries, by rw [← h]; exact w.isODHom⟩

@[scoped simp] theorem castHom_toSeries {X X' : FormalODModule q A} (h : X = X') {Y : FormalODModule q A}
    (w : X.Hom Y) : (castHom h w).toSeries = w.toSeries := rfl

theorem castHom_isIso {X X' : FormalODModule q A} (h : X = X') {Y : FormalODModule q A}
    (w : X.Hom Y) (hw : w.IsIso) : (castHom h w).IsIso := by
  subst h
  have : castHom rfl w = w := FormalODModule.Hom.ext rfl
  rw [this]
  exact hw

def castHomT {Y Y' : FormalODModule q A} (h : Y = Y') {X : FormalODModule q A} (w : X.Hom Y) :
    X.Hom Y' :=
  ⟨w.toSeries, by rw [← h]; exact w.isODHom⟩

@[scoped simp] theorem castHomT_toSeries {Y Y' : FormalODModule q A} (h : Y = Y') {X : FormalODModule q A}
    (w : X.Hom Y) : (castHomT h w).toSeries = w.toSeries := rfl

theorem castHomT_isIso {Y Y' : FormalODModule q A} (h : Y = Y') {X : FormalODModule q A}
    (w : X.Hom Y) (hw : w.IsIso) : (castHomT h w).IsIso := by
  subst h
  have : castHomT rfl w = w := FormalODModule.Hom.ext rfl
  rw [this]
  exact hw

theorem inverse_unique {s g₁ g₂ : Series A} (hs : ∀ i, constantCoeff (s i) = 0)
    (hg₂ : ∀ i, constantCoeff (g₂ i) = 0)
    (h₁ : g₁.comp s = Series.id A) (h₂ : s.comp g₂ = Series.id A) : g₁ = g₂ := by
  calc g₁ = g₁.comp (Series.id A) := (Series.comp_id _).symm
    _ = g₁.comp (s.comp g₂) := by rw [h₂]
    _ = (g₁.comp s).comp g₂ := (Series.comp_assoc _ _ _ hs hg₂).symm
    _ = g₂ := by rw [h₁, Series.id_comp _ hg₂]

theorem isIso_comp {g : Y.Hom Z} {f : X.Hom Y} (hg : g.IsIso) (hf : f.IsIso) : (g.comp f).IsIso := by
  obtain ⟨g', hg'₁, hg'₂⟩ := hg
  obtain ⟨f', hf'₁, hf'₂⟩ := hf
  have e1 := congrArg FormalODModule.Hom.toSeries hg'₁
  have e2 := congrArg FormalODModule.Hom.toSeries hg'₂
  have e3 := congrArg FormalODModule.Hom.toSeries hf'₁
  have e4 := congrArg FormalODModule.Hom.toSeries hf'₂
  simp only [comp_toSeries, id_toSeries] at e1 e2 e3 e4
  refine ⟨f'.comp g', FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩
  · show (f'.toSeries.comp g'.toSeries).comp (g.toSeries.comp f.toSeries) = Series.id A
    rw [Series.comp_assoc _ _ _ (hom_cc g') (Series.constantCoeff_comp (hom_cc g) (hom_cc f)),
      ← Series.comp_assoc g'.toSeries _ _ (hom_cc g) (hom_cc f), e1, Series.id_comp _ (hom_cc f), e3]
  · show (g.toSeries.comp f.toSeries).comp (f'.toSeries.comp g'.toSeries) = Series.id A
    rw [Series.comp_assoc _ _ _ (hom_cc f) (Series.constantCoeff_comp (hom_cc f') (hom_cc g')),
      ← Series.comp_assoc f.toSeries _ _ (hom_cc f') (hom_cc g'), e4, Series.id_comp _ (hom_cc g'), e2]

theorem isIso_map (r : A →+* A') {f : X.Hom Y} (hf : f.IsIso) : (f.map r).IsIso := by
  obtain ⟨f', hf'₁, hf'₂⟩ := hf
  have e3 := congrArg FormalODModule.Hom.toSeries hf'₁
  have e4 := congrArg FormalODModule.Hom.toSeries hf'₂
  simp only [comp_toSeries, id_toSeries] at e3 e4
  refine ⟨f'.map r, FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩
  · show (f'.toSeries.map r).comp (f.toSeries.map r) = Series.id A'
    rw [← Series.map_comp r _ _ (hom_cc f), e3, Series.map_id]
  · show (f.toSeries.map r).comp (f'.toSeries.map r) = Series.id A'
    rw [← Series.map_comp r _ _ (hom_cc f'), e4, Series.map_id]

theorem exists_inv {f : X.Hom Y} (hf : f.IsIso) :
    ∃ g : Y.Hom X, g.toSeries.comp f.toSeries = Series.id A ∧ f.toSeries.comp g.toSeries = Series.id A := by
  obtain ⟨g, hg₁, hg₂⟩ := hf
  have e1 := congrArg FormalODModule.Hom.toSeries hg₁
  have e2 := congrArg FormalODModule.Hom.toSeries hg₂
  simp only [comp_toSeries, id_toSeries] at e1 e2
  exact ⟨g, e1, e2⟩

end homs

section dualmap

variable {k k' : Type} [CommRing k] [CommRing k']

def dualMap (f : k →+* k') : DualNumber k →+* DualNumber k' where
  toFun t := ((f (TrivSqZeroExt.fst t), f (TrivSqZeroExt.snd t)) : DualNumber k')
  map_one' := by ext <;> simp
  map_mul' s t := by
    ext
    · simp [TrivSqZeroExt.fst_mul]
    · simp [mul_comm]
  map_zero' := by ext <;> simp
  map_add' s t := by ext <;> simp

@[scoped simp] theorem fst_dualMap (f : k →+* k') (t : DualNumber k) :
    TrivSqZeroExt.fst (dualMap f t) = f (TrivSqZeroExt.fst t) := rfl

@[scoped simp] theorem snd_dualMap (f : k →+* k') (t : DualNumber k) :
    TrivSqZeroExt.snd (dualMap f t) = f (TrivSqZeroExt.snd t) := rfl

theorem dualMap_comp_dualMap {k'' : Type} [CommRing k''] (g : k' →+* k'') (f : k →+* k') :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun _ => rfl

theorem dualMap_id : dualMap (RingHom.id k) = RingHom.id (DualNumber k) :=
  RingHom.ext fun _ => rfl

theorem fstHom_comp_dualMap (f : k →+* k') :
    (TrivSqZeroExt.fstHom k' k' k').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom k k k).toRingHom :=
  RingHom.ext fun _ => rfl

theorem dualMap_comp_inl (f : k →+* k') :
    (dualMap f).comp (algebraMap k (DualNumber k)) = (algebraMap k' (DualNumber k')).comp f :=
  RingHom.ext fun a => TrivSqZeroExt.ext rfl (by show f 0 = 0; exact map_zero f)

end dualmap

section node

variable {A : Type} [CommRing A] {B : Type} [CommRing B]

theorem linearPart_map (f : B →+* A) (φ : Series B) :
    MvFormalGroup.linearPart (φ.map f) = (MvFormalGroup.linearPart φ).map f := by
  ext i j
  simp [MvFormalGroup.linearPart, Series.map, MvPowerSeries.coeff_map]

theorem linearPart_varpi_eq_zero_of_node (j : Zp2 q →+* B) (X : FormalODModule q B) (hX : X.IsSpecial j)
    (h₀ : ∀ m ∈ X.lieZero j, Matrix.mulVecLin (MvFormalGroup.linearPart X.varpi) m = 0)
    (h₁ : ∀ m ∈ X.lieOne j, Matrix.mulVecLin (MvFormalGroup.linearPart X.varpi) m = 0) :
    MvFormalGroup.linearPart X.varpi = 0 := by
  have htop : X.lieZero j ⊔ X.lieOne j = ⊤ := hX.1.sup_eq_top
  have hall : ∀ m : X.Lie, Matrix.mulVecLin (MvFormalGroup.linearPart X.varpi) m = 0 := by
    intro m
    have hm : m ∈ X.lieZero j ⊔ X.lieOne j := htop.symm ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
    rw [map_add, h₀ y hy, h₁ z hz, add_zero]
  ext i l
  have := congrFun (hall (Pi.single l 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

theorem node_of_linearPart_varpi_eq_zero (j : Zp2 q →+* B) (X : FormalODModule q B)
    (h : MvFormalGroup.linearPart X.varpi = 0) :
    (∀ m ∈ X.lieZero j, Matrix.mulVecLin (MvFormalGroup.linearPart X.varpi) m = 0) ∧
    (∀ m ∈ X.lieOne j, Matrix.mulVecLin (MvFormalGroup.linearPart X.varpi) m = 0) := by
  constructor <;> intro m _ <;> simp [h]

end node

section transport

theorem map_act {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (X : FormalODModule q B) (a : Zp2 q) :
    (X.map f).act a = (X.act a).map f := rfl

theorem map_varpi {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (X : FormalODModule q B) :
    (X.map f).varpi = X.varpi.map f := rfl

variable {k : Type} [Field k] {kO : Type} [Field kO]

def transportBase {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (f : k →+* kO)
    {j₁ : Zp2 q →+* kO} (hj : j₁ = f.comp j₀) : SpecialFormalODModule q j₁ where
  toFormalODModule := X₀.toFormalODModule.map f
  isSpecial := by
    rw [hj]
    exact CerednikDrinfeld.FormalODModule.IsSpecial.map j₀ f X₀.toFormalODModule X₀.isSpecial
  hasHeight := by
    show FormalODModule.HasKernelOfDegree ((X₀.toFormalODModule.map f).act (q : Zp2 q)) (q ^ 4)
    rw [map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f (X₀.act (q : Zp2 q))
      (X₀.isLawHom_act (q : Zp2 q)).1 X₀.hasHeight

@[scoped simp] theorem transportBase_toFormalODModule {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (f : k →+* kO)
    {j₁ : Zp2 q →+* kO} (hj : j₁ = f.comp j₀) :
    (transportBase X₀ f hj).toFormalODModule = X₀.toFormalODModule.map f := rfl

end transport

section testalg

variable (k : Type) [Field k]

abbrev PP : Type := TrivSqZeroExt k (k × k)

def prodEquivTsze (M : Type) [AddCommGroup M] [Module k M] : (k × M) ≃ₗ[k] TrivSqZeroExt k M :=
  { toFun := fun x => x, invFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
    left_inv := fun _ => rfl, right_inv := fun _ => rfl }

scoped instance finite_dual : Module.Finite k (DualNumber k) := Module.Finite.equiv (prodEquivTsze k k)

scoped instance finite_PP : Module.Finite k (PP k) := Module.Finite.equiv (prodEquivTsze k (k × k))

scoped instance artinian_dual : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k _

scoped instance artinian_PP : IsArtinianRing (PP k) := IsArtinianRing.of_finite k _

scoped instance isLocalRing_PP : IsLocalRing (PP k) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases h : TrivSqZeroExt.fst a = 0
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h, sub_zero]
    exact isUnit_one
  · left
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact Ne.isUnit h

def π₁ : PP k →ₐ[k] DualNumber k := TrivSqZeroExt.map (LinearMap.fst k k k)
def π₂ : PP k →ₐ[k] DualNumber k := TrivSqZeroExt.map (LinearMap.snd k k k)
def σP : PP k →ₐ[k] DualNumber k := TrivSqZeroExt.map (LinearMap.fst k k k + LinearMap.snd k k k)

@[scoped simp] theorem fst_π₁ (t : PP k) : TrivSqZeroExt.fst (π₁ k t) = TrivSqZeroExt.fst t := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem fst_π₂ (t : PP k) : TrivSqZeroExt.fst (π₂ k t) = TrivSqZeroExt.fst t := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem fst_σP (t : PP k) : TrivSqZeroExt.fst (σP k t) = TrivSqZeroExt.fst t := TrivSqZeroExt.fst_map _ _
@[scoped simp] theorem snd_π₁ (t : PP k) : TrivSqZeroExt.snd (π₁ k t) = (TrivSqZeroExt.snd t).1 := TrivSqZeroExt.snd_map _ _
@[scoped simp] theorem snd_π₂ (t : PP k) : TrivSqZeroExt.snd (π₂ k t) = (TrivSqZeroExt.snd t).2 := TrivSqZeroExt.snd_map _ _
@[scoped simp] theorem snd_σP (t : PP k) : TrivSqZeroExt.snd (σP k t) = (TrivSqZeroExt.snd t).1 + (TrivSqZeroExt.snd t).2 :=
  TrivSqZeroExt.snd_map _ _

variable {k}

def toPP {B : Type} [CommRing B] (p₁ p₂ : B →+* DualNumber k)
    (h : ∀ b, TrivSqZeroExt.fst (p₂ b) = TrivSqZeroExt.fst (p₁ b)) : B →+* PP k where
  toFun b := ((TrivSqZeroExt.fst (p₁ b), (TrivSqZeroExt.snd (p₁ b), TrivSqZeroExt.snd (p₂ b))) : PP k)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp [TrivSqZeroExt.fst_mul]
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul]
      simp [smul_eq_mul]
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul]
      simp [smul_eq_mul, h]

theorem π₁_comp_toPP {B : Type} [CommRing B] (p₁ p₂ : B →+* DualNumber k)
    (h : ∀ b, TrivSqZeroExt.fst (p₂ b) = TrivSqZeroExt.fst (p₁ b)) :
    (π₁ k).toRingHom.comp (toPP p₁ p₂ h) = p₁ :=
  RingHom.ext fun b => TrivSqZeroExt.ext (by simp [toPP, π₁]) (by simp [toPP, π₁])

theorem π₂_comp_toPP {B : Type} [CommRing B] (p₁ p₂ : B →+* DualNumber k)
    (h : ∀ b, TrivSqZeroExt.fst (p₂ b) = TrivSqZeroExt.fst (p₁ b)) :
    (π₂ k).toRingHom.comp (toPP p₁ p₂ h) = p₂ :=
  RingHom.ext fun b => TrivSqZeroExt.ext (by simp [toPP, π₂, h]) (by simp [toPP, π₂])

theorem σP_comp_toPP {B : Type} [CommRing B] (p₁ p₂ σ : B →+* DualNumber k)
    (h : ∀ b, TrivSqZeroExt.fst (p₂ b) = TrivSqZeroExt.fst (p₁ b))
    (hσ₁ : ∀ b, TrivSqZeroExt.fst (σ b) = TrivSqZeroExt.fst (p₁ b))
    (hσ₂ : ∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) :
    (σP k).toRingHom.comp (toPP p₁ p₂ h) = σ :=
  RingHom.ext fun b => TrivSqZeroExt.ext (by simp [toPP, σP, hσ₁]) (by simp [toPP, σP, hσ₂])

end testalg

section hull

variable {k : Type} [Field k] [CharP k q] [IsAlgClosed k] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
variable {Onr : Type} [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr]
variable (e : IsLocalRing.ResidueField Onr ≃+* k)
variable {ι : Zp2 q →+* Onr} (hι : (IsLocalRing.residue Onr).comp ι = (e.symm : k →+* IsLocalRing.ResidueField Onr).comp j₀)

abbrev X₀' : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι) :=
  transportBase X₀ (e.symm : k →+* IsLocalRing.ResidueField Onr) hι

variable {R : Type} [CommRing R] [Algebra Onr R]
variable (resR : R →+* IsLocalRing.ResidueField Onr)
variable (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom (X₀' X₀ e hι).toFormalODModule)

@[reducible] def algOnr (A : Type) [CommRing A] [Algebra k A] : Algebra Onr A :=
  ((algebraMap k A).comp ((e : IsLocalRing.ResidueField Onr →+* k).comp (IsLocalRing.residue Onr))).toAlgebra

abbrev resO (A : Type) [CommRing A] (resk : A →+* k) : A →+* IsLocalRing.ResidueField Onr :=
  (e.symm : k →+* IsLocalRing.ResidueField Onr).comp resk

theorem resO_surjective (A : Type) [CommRing A] (resk : A →+* k) (hs : Function.Surjective resk) :
    Function.Surjective (resO e A resk) :=
  e.symm.surjective.comp hs

theorem resO_comp_algebraMap (A : Type) [CommRing A] [Algebra k A] (resk : A →+* k)
    (hresk : resk.comp (algebraMap k A) = RingHom.id k) :
    letI : Algebra Onr A := algOnr e A
    (resO e A resk).comp (algebraMap Onr A) = IsLocalRing.residue Onr := by
  ext o
  show e.symm (resk (algebraMap k A (e (IsLocalRing.residue Onr o)))) = IsLocalRing.residue Onr o
  rw [show resk (algebraMap k A (e (IsLocalRing.residue Onr o))) = e (IsLocalRing.residue Onr o) from
    RingHom.congr_fun hresk _, RingEquiv.symm_apply_apply]

def wO (A : Type) [CommRing A] (resk : A →+* k) (X : FormalODModule q A)
    (w : (X.map resk).Hom X₀.toFormalODModule) :
    (X.map (resO e A resk)).Hom (X₀' X₀ e hι).toFormalODModule :=
  castHom (FormalODModule.map_map resk (e.symm : k →+* IsLocalRing.ResidueField Onr) X)
    (w.map (e.symm : k →+* IsLocalRing.ResidueField Onr))

theorem wO_toSeries (A : Type) [CommRing A] (resk : A →+* k) (X : FormalODModule q A)
    (w : (X.map resk).Hom X₀.toFormalODModule) :
    (wO X₀ e hι A resk X w).toSeries = w.toSeries.map (e.symm : k →+* IsLocalRing.ResidueField Onr) := rfl

theorem wO_isIso (A : Type) [CommRing A] (resk : A →+* k) (X : FormalODModule q A)
    (w : (X.map resk).Hom X₀.toFormalODModule) (hw : w.IsIso) : (wO X₀ e hι A resk X w).IsIso :=
  castHom_isIso _ _ (isIso_map _ hw)

def IsClass (A : Type) [CommRing A] [Algebra k A] (resk : A →+* k) (X : FormalODModule q A)
    (w : (X.map resk).Hom X₀.toFormalODModule) (χ : R →+* A) : Prop :=
  resk.comp χ = (e : IsLocalRing.ResidueField Onr →+* k).comp resR ∧
  χ.comp (algebraMap Onr R) = (algebraMap k A).comp ((e : IsLocalRing.ResidueField Onr →+* k).comp (IsLocalRing.residue Onr)) ∧
  ∃ v : (Xu.map χ).Hom X, v.IsIso ∧ (w.comp (v.map resk)).toSeries = wu.toSeries.map (e : IsLocalRing.ResidueField Onr →+* k)

variable (hPRO : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
    (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
    resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
  ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
  ∀ (w : (X.map resA).Hom (X₀' X₀ e hι).toFormalODModule), w.IsIso →
    ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
      ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
        (w.comp (v.map resA)).toSeries = wu.toSeries)

include hPRO in

theorem classify (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra k A]
    (resk : A →+* k) (hs : Function.Surjective resk) (hresk : resk.comp (algebraMap k A) = RingHom.id k)
    (X : FormalODModule q A) (w : (X.map resk).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    (∃ χ : R →+* A, IsClass X₀ e hι resR Xu wu A resk X w χ) ∧
    (∀ χ χ' : R →+* A, IsClass X₀ e hι resR Xu wu A resk X w χ → IsClass X₀ e hι resR Xu wu A resk X w χ' → χ = χ') := by
  letI : Algebra Onr A := algOnr e A
  have hcomp := resO_comp_algebraMap e A resk hresk
  have hsurj := resO_surjective e A resk hs
  have hXw := CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing Onr ι
    (X₀' X₀ e hι) A (resO e A resk) hsurj hcomp X (wO X₀ e hι A resk X w) (wO_isIso X₀ e hι A resk X w hw)
  have H := hPRO A (resO e A resk) hsurj hcomp X hXw.1 hXw.2 (wO X₀ e hι A resk X w) (wO_isIso X₀ e hι A resk X w hw)

  have key : ∀ (χ : R →+* A) (v : (Xu.map χ).Hom X),
      ((wO X₀ e hι A resk X w).comp (v.map (resO e A resk))).toSeries = wu.toSeries ↔
        (w.comp (v.map resk)).toSeries = wu.toSeries.map (e : IsLocalRing.ResidueField Onr →+* k) := by
    intro χ v
    have h1 : ((wO X₀ e hι A resk X w).comp (v.map (resO e A resk))).toSeries =
        ((w.comp (v.map resk)).toSeries).map (e.symm : k →+* IsLocalRing.ResidueField Onr) := by
      show (w.toSeries.map _).comp (v.toSeries.map ((e.symm : k →+* IsLocalRing.ResidueField Onr).comp resk)) = _
      rw [comp_toSeries, map_toSeries, Series.map_comp _ _ _ (cc_map (hom_cc v) resk), Series.map_map]
    rw [h1]
    constructor
    · intro h
      rw [← h, Series.map_map]
      have : ((e : IsLocalRing.ResidueField Onr →+* k).comp (e.symm : k →+* IsLocalRing.ResidueField Onr)) = RingHom.id k := by
        ext x; exact e.apply_symm_apply x
      rw [this, Series.map_ringHom_id]
    · intro h
      rw [h, Series.map_map]
      have : ((e.symm : k →+* IsLocalRing.ResidueField Onr).comp (e : IsLocalRing.ResidueField Onr →+* k)) =
          RingHom.id (IsLocalRing.ResidueField Onr) := by
        ext x; exact e.symm_apply_apply x
      rw [this, Series.map_ringHom_id]
  have key2 : ∀ χ : R →+* A, (resO e A resk).comp χ = resR ↔
      resk.comp χ = (e : IsLocalRing.ResidueField Onr →+* k).comp resR := by
    intro χ
    constructor
    · intro h; rw [← h]; ext r; exact (e.apply_symm_apply _).symm
    · intro h; ext r
      show e.symm (resk (χ r)) = resR r
      rw [show resk (χ r) = e (resR r) from RingHom.congr_fun h r, RingEquiv.symm_apply_apply]
  constructor
  · obtain ⟨χ, ⟨hχ₁, v, hv, hc⟩, -⟩ := H
    refine ⟨χ.toRingHom, (key2 _).1 hχ₁, χ.comp_algebraMap, v, hv, (key χ.toRingHom v).1 hc⟩
  · intro χ χ' ⟨h₁, h₂, v, hv, hc⟩ ⟨h₁', h₂', v', hv', hc'⟩
    let χa : R →ₐ[Onr] A := { toRingHom := χ, commutes' := fun o => RingHom.congr_fun h₂ o }
    let χa' : R →ₐ[Onr] A := { toRingHom := χ', commutes' := fun o => RingHom.congr_fun h₂' o }
    have := H.unique (y₁ := χa) (y₂ := χa') ⟨(key2 χ).2 h₁, v, hv, (key χ v).2 hc⟩ ⟨(key2 χ').2 h₁', v', hv', (key χ' v').2 hc'⟩
    exact congrArg AlgHom.toRingHom this

end hull

section linparts

variable {B : Type} [CommRing B]

theorem linearPart_comp (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (ψ.comp φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem linearPart_id' : MvFormalGroup.linearPart (Series.id B) = 1 := MvFormalGroup.linearPart_X

theorem linearPart_hom_mul_varpi {X Y : FormalODModule q B} (f : X.Hom Y) :
    MvFormalGroup.linearPart f.toSeries * MvFormalGroup.linearPart X.varpi =
      MvFormalGroup.linearPart Y.varpi * MvFormalGroup.linearPart f.toSeries := by
  rw [← linearPart_comp _ _ X.isLawHom_varpi.1, ← linearPart_comp _ _ (hom_cc f), f.isODHom.2.2]

theorem linearPart_inv {f g : Series B} (hf : ∀ i, constantCoeff (f i) = 0) (hg : ∀ i, constantCoeff (g i) = 0)
    (h₁ : g.comp f = Series.id B) (h₂ : f.comp g = Series.id B) :
    MvFormalGroup.linearPart g * MvFormalGroup.linearPart f = 1 ∧
      MvFormalGroup.linearPart f * MvFormalGroup.linearPart g = 1 := by
  constructor
  · rw [← linearPart_comp _ _ hf, h₁, linearPart_id']
  · rw [← linearPart_comp _ _ hg, h₂, linearPart_id']

end linparts

section dualmatrix

variable {k : Type} [CommRing k] {n : Type} [Fintype n] [DecidableEq n]

theorem matrix_eq_of_conj_of_fst (N A A' : Matrix n n (DualNumber k))
    (hN : N.map TrivSqZeroExt.fst = 1) (hA : A.map TrivSqZeroExt.fst = 0) (hA' : A'.map TrivSqZeroExt.fst = 0)
    (h : N * A = A' * N) : A = A' := by
  apply Matrix.ext; intro i j
  have hNij : ∀ i j, TrivSqZeroExt.fst (N i j) = (1 : Matrix n n k) i j := fun i j => by
    have := congrFun (congrFun hN i) j; simpa [Matrix.map_apply] using this
  have hAij : ∀ i j, TrivSqZeroExt.fst (A i j) = 0 := fun i j => by
    have := congrFun (congrFun hA i) j; simpa [Matrix.map_apply] using this
  have hA'ij : ∀ i j, TrivSqZeroExt.fst (A' i j) = 0 := fun i j => by
    have := congrFun (congrFun hA' i) j; simpa [Matrix.map_apply] using this
  have hij := congrFun (congrFun h i) j
  rw [Matrix.mul_apply, Matrix.mul_apply] at hij
  refine TrivSqZeroExt.ext ((hAij i j).trans (hA'ij i j).symm) ?_
  have hs := congrArg TrivSqZeroExt.snd hij
  simp only [TrivSqZeroExt.snd_sum, DualNumber.snd_mul, hNij, hAij, hA'ij, mul_zero, zero_mul, add_zero, zero_add,
    Matrix.one_apply, ite_mul, one_mul, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hs
  exact hs

theorem mulVec_eq_of_fst_eq (A : Matrix n n (DualNumber k)) (hA : A.map TrivSqZeroExt.fst = 0)
    (x y : n → DualNumber k) (hxy : ∀ i, TrivSqZeroExt.fst (x i) = TrivSqZeroExt.fst (y i)) :
    A.mulVec x = A.mulVec y := by
  have hAij : ∀ i j, TrivSqZeroExt.fst (A i j) = 0 := fun i j => by
    have := congrFun (congrFun hA i) j; simpa [Matrix.map_apply] using this
  funext i
  show ∑ j, A i j * x j = ∑ j, A i j * y j
  refine Finset.sum_congr rfl fun j _ => TrivSqZeroExt.ext ?_ ?_
  · simp [TrivSqZeroExt.fst_mul, hAij]
  · simp only [DualNumber.snd_mul, hAij, zero_mul, zero_add, hxy]

end dualmatrix

section basislemma

variable {R K : Type} [CommRing R] [Field K]

theorem exists_apply_ne_zero_of_basis (res : R →+* K) (f₀ f₁ : Fin 2 → R)
    (hbasis : ∀ m : Fin 2 → R, ∃! c : R × R, m = c.1 • f₀ + c.2 • f₁) :
    (∃ j, res (f₁ j) ≠ 0) ∧ (∃ j, res (f₀ j) ≠ 0) := by
  by_contra H
  rw [not_and_or, not_exists, not_exists] at H
  simp only [not_not] at H
  obtain ⟨c, hc, -⟩ := hbasis (Pi.single 0 1)
  obtain ⟨d, hd, -⟩ := hbasis (Pi.single 1 1)
  have hc0 := congrArg res (congrFun hc 0)
  have hc1 := congrArg res (congrFun hc 1)
  have hd0 := congrArg res (congrFun hd 0)
  have hd1 := congrArg res (congrFun hd 1)
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0),
    Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul, map_one, map_zero] at hc0 hc1 hd0 hd1
  rcases H with H | H
  ·
    rw [H 0] at hc0 hd0; rw [H 1] at hc1 hd1
    simp only [mul_zero, add_zero] at hc0 hc1 hd0 hd1

    have h1 : res (f₀ 1) ≠ 0 := fun h => by rw [h, mul_zero] at hd1; exact one_ne_zero hd1
    have h2 : res c.1 = 0 := by
      rcases mul_eq_zero.mp hc1.symm with h | h
      · exact h
      · exact absurd h h1
    rw [h2, zero_mul] at hc0; exact one_ne_zero hc0
  ·
    rw [H 0] at hc0 hd0; rw [H 1] at hc1 hd1
    simp only [mul_zero, zero_add] at hc0 hc1 hd0 hd1

    have h1 : res (f₁ 0) ≠ 0 := fun h => by rw [h, mul_zero] at hc0; exact one_ne_zero hc0
    have h2 : res d.2 = 0 := by
      rcases mul_eq_zero.mp hd0.symm with h | h
      · exact h
      · exact absurd h h1
    rw [h2, zero_mul] at hd1; exact one_ne_zero hd1

end basislemma

set_option maxHeartbeats 6400000 in
theorem mainQR (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    :
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ] (ψκ : WittVector p k →+* κ) (hκ : IsNilpotent (p : κ))
      (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
      (hresψ : ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp ψR = ψκ)
      (t t' : Rigidified p Φ (DualNumber κ)),
      t.IsAdmissible ι ψR → t'.IsAdmissible ι ψR →
      (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).IsIsomorphic
        (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)) →
      ∀ (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ)),
        t.IsCartierQuadruple ι hcΦ rΦ ψR Q → t'.IsCartierQuadruple ι hcΦ rΦ ψR Q' →
        Q.IsIsomorphic Q' → t.IsIsomorphic t' := by
  intro κ _ _ _ ψκ hκ ψR hR hresψ t t' ht ht' hiso Q Q' hQ hQ' hQQ'
  classical
  haveI hκp : CharP κ p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hκ.eq_zero
  have hFψ : ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp ψR = ψκ := hresψ
  have hsp : (t.X.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).IsSpecial (structureMap ι ψκ) := by
    have := CerednikDrinfeld.FormalODModule.IsSpecial.map (structureMap ι ψR) ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) t.X ht.1
    rwa [show ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp (structureMap ι ψR) = structureMap ι ψκ by
      show ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp (ψR.comp ι) = ψκ.comp ι; rw [← RingHom.comp_assoc, hFψ]] at this
  have hht : (t.X.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree ((t.X.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).act (p : Zp2 p)) (p ^ 4)
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) (t.X.act (p : Zp2 p)) (t.X.isLawHom_act _).1 ht.2.1
  let X₀ : SpecialFormalODModule p (structureMap ι ψκ) := ⟨t.X.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ), hsp, hht⟩

  obtain ⟨-, σ₀, σ₁, hQv⟩ := (Rigidified.isCartierQuadruple_iff_exists_via ι hcΦ rΦ ψR t Q).1 hQ
  obtain ⟨-, σ₀', σ₁', hQv'⟩ := (Rigidified.isCartierQuadruple_iff_exists_via ι hcΦ rΦ ψR t' Q').1 hQ'
  obtain ⟨I⟩ := hQQ'

  obtain ⟨u₀, v₀, m, hu₀, hv₀, hvu, huv, hρ, Λ, hΛσ₀, hΛσ₁, hΛ0g, hΛ1g, hLamPi, hΛred⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ κ ψR hR t t' ht ht' Q Q' σ₀ σ₁ hQv σ₀' σ₁' hQv' I hiso
  let w : ((t.X).map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Hom X₀.toFormalODModule := FormalODModule.Hom.id _
  have hw : w.IsIso := id_isIso _
  let w' : ((t'.X).map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Hom X₀.toFormalODModule := ⟨v₀, hv₀⟩
  have hw' : w'.IsIso := ⟨⟨u₀, hu₀⟩, FormalODModule.Hom.ext huv, FormalODModule.Hom.ext hvu⟩
  by_cases hnode : ((∀ mm ∈ X₀.toFormalODModule.lieZero (structureMap ι ψκ), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) mm = 0) ∧
      (∀ mm ∈ X₀.toFormalODModule.lieOne (structureMap ι ψκ), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) mm = 0))
  swap
  ·
    exact CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node
      p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ κ ψR hR t t' ht ht' Q Q' σ₀ σ₁ hQv σ₀' σ₁' hQv' Λ ψκ hresψ hnode
      u₀ v₀ m hu₀ hv₀ hvu huv hρ hΛ0g hΛ1g hLamPi hΛred (fun x => ⟨I.N₀_eq x, I.N₁_eq x⟩)
      (fun x i v f hf hc hcb hcΦf L hL z hz mm hm f' hf' hc' hcb' hcΦf' L' hL' z' hz' mm' hm' =>
        CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.awayToLoc_tangent_eq_sum_of_iso
          p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ κ ψR hR t t' ht ht' Q Q' σ₀ σ₁ hQv σ₀' σ₁' hQv' Λ I hΛσ₀ hΛσ₁
          x i v f hf hc hcb hcΦf L hL z hz mm hm f' hf' hc' hcb' hcΦf' L' hL' z' hz' mm' hm')

  obtain ⟨Onr, _, _, _, _, _, hOc, hOm, e, ι₀, O', _, _, _, _, _, _, ϖ', _, _, φ', -, -⟩ :=
    WittVector.exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_ringHom_and_sq_eq_of_isAlgClosed p κ
  haveI : IsAlgClosed (IsLocalRing.ResidueField Onr) := IsAlgClosed.of_ringEquiv κ _ e.symm
  haveI : CharP (IsLocalRing.ResidueField Onr) p := charP_of_injective_ringHom (e.symm : κ →+* IsLocalRing.ResidueField Onr).injective p
  have hmax : Ideal.span {algebraMap ℤ_[p] Onr (p : ℤ_[p])} = IsLocalRing.maximalIdeal Onr := IsLocalRing.eq_maximalIdeal hOm
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal Onr) Onr := hmax ▸ hOc

  obtain ⟨ι', hι'⟩ : ∃ ι' : Zp2 p →+* Onr,
      (IsLocalRing.residue Onr).comp ι' = (e.symm : κ →+* IsLocalRing.ResidueField Onr).comp (structureMap ι ψκ) := by
    rcases WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two_of_charP p (IsLocalRing.ResidueField Onr)
        ((e.symm : κ →+* IsLocalRing.ResidueField Onr).comp (structureMap ι ψκ)) ((IsLocalRing.residue Onr).comp ι₀) with h | h
    · exact ⟨ι₀, h.symm⟩
    · exact ⟨ι₀.comp WittVector.frobenius, by rw [← RingHom.comp_assoc, ← h]⟩

  obtain ⟨R, _, _, _, _, _, resR, hresR, Xu, wu, hwu, hPRO⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations Onr ι' (X₀' X₀ e hι')

  have hresk : ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp (algebraMap κ (DualNumber κ)) = RingHom.id κ := RingHom.ext fun _ => rfl
  have hsk : Function.Surjective ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  obtain ⟨⟨χ, hχcl⟩, huniq⟩ := classify X₀ e hι' resR Xu wu hPRO (DualNumber κ) ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) hsk hresk t.X w hw
  obtain ⟨⟨χ', hχcl'⟩, huniq'⟩ := classify X₀ e hι' resR Xu wu hPRO (DualNumber κ) ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) hsk hresk t'.X w' hw'
  have ee : ((e : IsLocalRing.ResidueField Onr →+* κ).comp (e.symm : κ →+* IsLocalRing.ResidueField Onr)) = RingHom.id κ := by ext x; exact e.apply_symm_apply x
  have ee' : ((e.symm : κ →+* IsLocalRing.ResidueField Onr).comp (e : IsLocalRing.ResidueField Onr →+* κ)) = RingHom.id (IsLocalRing.ResidueField Onr) := by ext x; exact e.symm_apply_apply x

  have lift : ∀ χ : R →+* DualNumber κ, ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp χ = (e : IsLocalRing.ResidueField Onr →+* κ).comp resR →
      χ.comp (algebraMap Onr R) = (algebraMap κ (DualNumber κ)).comp ((e : IsLocalRing.ResidueField Onr →+* κ).comp (IsLocalRing.residue Onr)) →
      ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp ((dualMap (e.symm : κ →+* IsLocalRing.ResidueField Onr)).comp χ) = resR ∧
        ((dualMap (e.symm : κ →+* IsLocalRing.ResidueField Onr)).comp χ).comp (algebraMap Onr R) =
          (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) := by
    intro χ h1 h2
    constructor
    · have : (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp (dualMap (e.symm : κ →+* IsLocalRing.ResidueField Onr)) = (e.symm : κ →+* IsLocalRing.ResidueField Onr).comp ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) := RingHom.ext fun _ => rfl
      rw [← RingHom.comp_assoc, this, RingHom.comp_assoc, h1, ← RingHom.comp_assoc, ee', RingHom.id_comp]
    · ext o
      · show e.symm (TrivSqZeroExt.fst (χ (algebraMap Onr R o))) = TrivSqZeroExt.fst (algebraMap _ (DualNumber (IsLocalRing.ResidueField Onr)) (IsLocalRing.residue Onr o))
        rw [show χ (algebraMap Onr R o) = algebraMap κ (DualNumber κ) (e (IsLocalRing.residue Onr o)) from RingHom.congr_fun h2 o]
        exact e.symm_apply_apply _
      · show e.symm (TrivSqZeroExt.snd (χ (algebraMap Onr R o))) = TrivSqZeroExt.snd (algebraMap _ (DualNumber (IsLocalRing.ResidueField Onr)) (IsLocalRing.residue Onr o))
        rw [show χ (algebraMap Onr R o) = algebraMap κ (DualNumber κ) (e (IsLocalRing.residue Onr o)) from RingHom.congr_fun h2 o]
        show e.symm (0 : κ) = 0
        exact map_zero _
  have cancel : ∀ χ : R →+* DualNumber κ, (dualMap (e : IsLocalRing.ResidueField Onr →+* κ)).comp ((dualMap (e.symm : κ →+* IsLocalRing.ResidueField Onr)).comp χ) = χ := by
    intro χ
    rw [← RingHom.comp_assoc, dualMap_comp_dualMap, ee, dualMap_id, RingHom.id_comp]

  have hker : ∀ r ∈ IsLocalRing.maximalIdeal R, resR r = 0 := by
    intro r hr
    have hsurjres : Function.Surjective resR := fun x => by
      obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
      exact ⟨algebraMap Onr R o, RingHom.congr_fun hresR o⟩
    have hmaxker : (RingHom.ker resR).IsMaximal := RingHom.ker_isMaximal_of_surjective resR hsurjres
    have := IsLocalRing.eq_maximalIdeal hmaxker
    rw [← this] at hr
    exact hr

  have hχχ : χ = χ' := by
    obtain ⟨h1, h2, vX, hvX, hcX⟩ := id hχcl
    obtain ⟨h1', h2', vX', hvX', hcX'⟩ := id hχcl'

    have e0 : vX.toSeries.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = wu.toSeries.map (e : IsLocalRing.ResidueField Onr →+* κ) := by
      have := hcX
      simp only [comp_toSeries, map_toSeries] at this
      rw [← this]; exact (Series.id_comp _ (cc_map (hom_cc vX) _)).symm
    have e1 : vX'.toSeries.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = u₀.comp (wu.toSeries.map (e : IsLocalRing.ResidueField Onr →+* κ)) := by
      have := hcX'
      simp only [comp_toSeries, map_toSeries] at this
      rw [← this, ← Series.comp_assoc u₀ v₀ _ hv₀.constantCoeff (cc_map (hom_cc vX') _), huv,
        Series.id_comp _ (cc_map (hom_cc vX') _)]
    have hfst : ∀ r, TrivSqZeroExt.fst (χ r) = TrivSqZeroExt.fst (χ' r) := fun r =>
      (RingHom.congr_fun h1 r).trans (RingHom.congr_fun h1' r).symm
    have hfst0 : ∀ r ∈ IsLocalRing.maximalIdeal R, TrivSqZeroExt.fst (χ r) = 0 := fun r hr => by
      rw [show TrivSqZeroExt.fst (χ r) = e (resR r) from RingHom.congr_fun h1 r, hker r hr, map_zero]
    have hlin0 : MvFormalGroup.linearPart X₀.varpi = 0 :=
      linearPart_varpi_eq_zero_of_node _ X₀.toFormalODModule X₀.isSpecial hnode.1 hnode.2
    have hlin0' : MvFormalGroup.linearPart (X₀' X₀ e hι').varpi = 0 := by
      show MvFormalGroup.linearPart (X₀.toFormalODModule.map _).varpi = 0
      rw [map_varpi, linearPart_map, hlin0]; ext i j; simp
    obtain ⟨hn0', hn1'⟩ := node_of_linearPart_varpi_eq_zero ((IsLocalRing.residue Onr).comp ι')
      (X₀' X₀ e hι').toFormalODModule hlin0'
    obtain ⟨f₀, f₁, u, v, hf₀, hf₁, hbasis, hu, hv, huv', humem, hvmem⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
        Onr hOc hOm ι' (X₀' X₀ e hι') R resR hresR Xu wu hwu hPRO hn0' hn1'
    have hinjχ := CerednikDrinfeld.SpecialFormalODModule.ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
        Onr hOc hOm ι' (X₀' X₀ e hι') R resR hresR Xu wu hwu hPRO hn0' hn1' f₀ f₁ u v hf₀ hf₁ hbasis hu hv

    have hPres : (MvFormalGroup.linearPart Xu.varpi).map resR = 0 := by
      obtain ⟨gw, hgw1, hgw2⟩ := hwu
      have hi := linearPart_hom_mul_varpi wu
      rw [map_varpi, linearPart_map] at hi
      have hinv := linearPart_inv (hom_cc wu) (hom_cc gw) (congrArg FormalODModule.Hom.toSeries hgw1)
        (congrArg FormalODModule.Hom.toSeries hgw2)
      calc (MvFormalGroup.linearPart Xu.varpi).map resR
          = (MvFormalGroup.linearPart gw.toSeries * MvFormalGroup.linearPart wu.toSeries) *
              (MvFormalGroup.linearPart Xu.varpi).map resR := by rw [hinv.1, one_mul]
        _ = MvFormalGroup.linearPart gw.toSeries * (MvFormalGroup.linearPart (X₀' X₀ e hι').varpi *
              MvFormalGroup.linearPart wu.toSeries) := by rw [Matrix.mul_assoc, hi]
        _ = 0 := by rw [hlin0', zero_mul, mul_zero]
    have hPF : ∀ χ₁ : R →+* DualNumber κ, ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp χ₁ = (e : IsLocalRing.ResidueField Onr →+* κ).comp resR →
        ((MvFormalGroup.linearPart Xu.varpi).map χ₁).map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = 0 := by
      intro χ₁ hχ₁
      rw [Matrix.map_map, show (⇑((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) ∘ ⇑χ₁) = ⇑((e : IsLocalRing.ResidueField Onr →+* κ).comp resR) from
        (congrArg (fun f : R →+* κ => (f : R → κ)) hχ₁ : _), RingHom.coe_comp, ← Matrix.map_map, hPres]
      ext i j; simp

    have hΛmat : LinearMap.toMatrix' Λ.toLinearMap * MvFormalGroup.linearPart t.X.varpi =
        MvFormalGroup.linearPart t'.X.varpi * LinearMap.toMatrix' Λ.toLinearMap := by
      apply Matrix.ext; intro i j
      have h := hLamPi (Pi.single j 1)
      have h' : (LinearMap.toMatrix' Λ.toLinearMap).mulVec ((MvFormalGroup.linearPart t.X.varpi).mulVec (Pi.single j 1)) =
          (MvFormalGroup.linearPart t'.X.varpi).mulVec ((LinearMap.toMatrix' Λ.toLinearMap).mulVec (Pi.single j 1)) := by
        rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]; exact h
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h'
      exact congrFun h' i
    have hΛF : (LinearMap.toMatrix' Λ.toLinearMap).map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = MvFormalGroup.linearPart u₀ := by
      apply Matrix.ext; intro i j
      rw [Matrix.map_apply, LinearMap.toMatrix'_apply]
      show TrivSqZeroExt.fst (Λ (Pi.single j 1) i) = _
      rw [hΛred]
      have : (fun j' => TrivSqZeroExt.fst ((Pi.single j 1 : t.X.Lie) j')) = Pi.single j (1 : κ) := by
        funext j'; by_cases hj : j' = j
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      rw [this, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl

    obtain ⟨g', hg'1, hg'2⟩ := hvX'
    have hiX := linearPart_hom_mul_varpi vX
    have hiG := linearPart_hom_mul_varpi g'
    rw [map_varpi, linearPart_map] at hiX hiG

    have hN : (MvFormalGroup.linearPart g'.toSeries * LinearMap.toMatrix' Λ.toLinearMap * MvFormalGroup.linearPart vX.toSeries) *
          (MvFormalGroup.linearPart Xu.varpi).map χ =
        (MvFormalGroup.linearPart Xu.varpi).map χ' *
          (MvFormalGroup.linearPart g'.toSeries * LinearMap.toMatrix' Λ.toLinearMap * MvFormalGroup.linearPart vX.toSeries) := by
      rw [Matrix.mul_assoc, hiX, ← Matrix.mul_assoc, Matrix.mul_assoc (MvFormalGroup.linearPart g'.toSeries), hΛmat,
        ← Matrix.mul_assoc, hiG, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

    have hNF : (MvFormalGroup.linearPart g'.toSeries * LinearMap.toMatrix' Λ.toLinearMap *
          MvFormalGroup.linearPart vX.toSeries).map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = 1 := by
      rw [Matrix.map_mul, Matrix.map_mul, hΛF, ← linearPart_map, ← linearPart_map, e0,
        Matrix.mul_assoc, ← linearPart_comp _ _ (cc_map (hom_cc wu) _), ← e1,
        ← linearPart_comp _ _ (cc_map (hom_cc vX') _), ← Series.map_comp _ _ _ (hom_cc vX'),
        show g'.toSeries.comp vX'.toSeries = Series.id _ from congrArg FormalODModule.Hom.toSeries hg'1, Series.map_id,
        linearPart_id']
    have hFcoe : (⇑((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) : DualNumber κ → κ) = TrivSqZeroExt.fst := rfl
    have hPeq : (MvFormalGroup.linearPart Xu.varpi).map χ = (MvFormalGroup.linearPart Xu.varpi).map χ' := by
      apply matrix_eq_of_conj_of_fst _ _ _ (hFcoe ▸ hNF) (hFcoe ▸ hPF χ h1) (hFcoe ▸ hPF χ' h1') hN

    obtain ⟨⟨j₁, hj₁⟩, ⟨j₀, hj₀⟩⟩ := exists_apply_ne_zero_of_basis resR f₀ f₁ hbasis
    have key : ∀ (f g : Fin 2 → R) (c : R) (hc : c ∈ IsLocalRing.maximalIdeal R)
        (hfg : Matrix.mulVecLin (MvFormalGroup.linearPart Xu.varpi) f = c • g) (j : Fin 2) (hj : resR (g j) ≠ 0),
        χ c = χ' c := by
      intro f g c hc hfg j hj
      have hmv : ∀ χ₁ : R →+* DualNumber κ, ((MvFormalGroup.linearPart Xu.varpi).map χ₁).mulVec (χ₁ ∘ f) = fun i => χ₁ c * χ₁ (g i) := by
        intro χ₁; funext i
        rw [← RingHom.map_mulVec, ← map_mul]; congr 1
        have := congrFun hfg i
        simpa [Matrix.mulVecLin_apply, Pi.smul_apply, smul_eq_mul] using this
      have hL : ((MvFormalGroup.linearPart Xu.varpi).map χ).mulVec (χ ∘ f) = ((MvFormalGroup.linearPart Xu.varpi).map χ').mulVec (χ' ∘ f) := by
        rw [hPeq]; exact mulVec_eq_of_fst_eq _ (hFcoe ▸ hPF χ' h1') _ _ (fun i => hfst (f i))
      rw [hmv χ, hmv χ'] at hL
      have hj' := congrArg TrivSqZeroExt.snd (congrFun hL j)
      rw [DualNumber.snd_mul, DualNumber.snd_mul, hfst0 c hc, zero_mul, zero_add,
        show TrivSqZeroExt.fst (χ' c) = 0 from (hfst c).symm.trans (hfst0 c hc), zero_mul, zero_add, ← hfst (g j),
        show TrivSqZeroExt.fst (χ (g j)) = e (resR (g j)) from RingHom.congr_fun h1 (g j)] at hj'
      have hne : e (resR (g j)) ≠ 0 := fun h0 => hj (by simpa using congrArg e.symm h0)
      refine TrivSqZeroExt.ext (hfst c) (mul_right_cancel₀ hne hj')
    have hcu : χ u = χ' u := key f₀ f₁ u humem hu j₁ hj₁
    have hcv : χ v = χ' v := key f₁ f₀ v hvmem hv j₀ hj₀
    have H := hinjχ _ _ (lift χ h1 h2) (lift χ' h1' h2')
      (by show dualMap _ (χ u) = dualMap _ (χ' u); rw [hcu])
      (by show dualMap _ (χ v) = dualMap _ (χ' v); rw [hcv])
    rw [← cancel χ, ← cancel χ', H]

  obtain ⟨h1, h2, vX, hvX, hcX⟩ := hχcl
  obtain ⟨h1', h2', vX', hvX', hcX'⟩ := hχcl'
  obtain ⟨gX, hgX1, hgX2⟩ := hvX
  have hXX : Xu.map χ' = Xu.map χ := by rw [hχχ]
  let V : t.X.Hom t'.X := (castHom hXX vX').comp gX
  have hV : V.IsIso := isIso_comp (castHom_isIso _ _ hvX') ⟨vX, hgX2, hgX1⟩
  obtain ⟨Vi, hVi1, hVi2⟩ := hV
  have e0 := hcX; have e1 := hcX'
  simp only [comp_toSeries, map_toSeries] at e0 e1
  have hVF : V.toSeries.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = u₀ := by
    show ((vX'.toSeries).comp gX.toSeries).map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = u₀
    have hg' : vX.toSeries.comp gX.toSeries = Series.id _ := congrArg FormalODModule.Hom.toSeries hgX2
    have e0' : vX.toSeries.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = wu.toSeries.map (e : IsLocalRing.ResidueField Onr →+* κ) := by
      rw [← e0]; exact (Series.id_comp _ (cc_map (hom_cc vX) _)).symm
    have e1' : vX'.toSeries.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) = u₀.comp (wu.toSeries.map (e : IsLocalRing.ResidueField Onr →+* κ)) := by
      rw [← e1, ← Series.comp_assoc u₀ v₀ _ hv₀.constantCoeff (cc_map (hom_cc vX') _), huv,
        Series.id_comp _ (cc_map (hom_cc vX') _)]
    rw [Series.map_comp _ _ _ (hom_cc gX), e1', ← e0',
      Series.comp_assoc u₀ _ _ (cc_map (hom_cc vX) _) (cc_map (hom_cc gX) _),
      ← Series.map_comp _ _ _ (hom_cc gX), hg', Series.map_id, Series.comp_id]
  refine CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
    ι ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) hsk ?_ hR ψR t t' ht ht' V.toSeries Vi.toSeries V.isODHom Vi.isODHom
    (congrArg FormalODModule.Hom.toSeries hVi1) (congrArg FormalODModule.Hom.toSeries hVi2) m ?_
  ·
    refine ⟨2, ?_⟩
    rw [Submodule.zero_eq_bot, eq_bot_iff, pow_two, Ideal.mul_le]
    intro r hr s hs
    rw [RingHom.mem_ker] at hr hs
    change TrivSqZeroExt.fst r = 0 at hr
    change TrivSqZeroExt.fst s = 0 at hs
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · show TrivSqZeroExt.fst (r * s) = 0
      rw [TrivSqZeroExt.fst_mul, hr, zero_mul]
    · show TrivSqZeroExt.snd (r * s) = 0
      rw [DualNumber.snd_mul, hr, hs, zero_mul, mul_zero, add_zero]
  · rw [hVF]; exact hρ

end QuadRigidity
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent.QuadRigidity"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega in
open scoped PadicInt Padic in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    :
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ] (ψκ : WittVector p k →+* κ) (hκ : IsNilpotent (p : κ))
      (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
      (hresψ : ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ).comp ψR = ψκ)
      (t t' : Rigidified p Φ (DualNumber κ)),
      t.IsAdmissible ι ψR → t'.IsAdmissible ι ψR →
      (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).IsIsomorphic
        (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)) →
      ∀ (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ)),
        t.IsCartierQuadruple ι hcΦ rΦ ψR Q → t'.IsCartierQuadruple ι hcΦ rΦ ψR Q' →
        Q.IsIsomorphic Q' → t.IsIsomorphic t' :=
  QuadRigidity.mainQR p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ

end
end S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isCartierQuadruple_of_isIsomorphic_dualNumber_of_isNilpotent (solution)
