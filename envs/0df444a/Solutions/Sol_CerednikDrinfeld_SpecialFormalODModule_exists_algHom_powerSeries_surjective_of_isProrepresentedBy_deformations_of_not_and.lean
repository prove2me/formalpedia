-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_algHom_powerSeries_surjective_of_isProrepresentedBy_deformations_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b1dd741c-32a8-58b4-a686-08017bcb06ce

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
import Theorems.Thm_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
import Theorems.Thm_IsLocalRing_surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_powerSeries_surjective_of_isProrepresentedBy_deformations_of_not_and
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open IsLocalRing

namespace DDF4

noncomputable def rho {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) : PowerSeries O →+* DualNumber k where
  toFun f := TrivSqZeroExt.inl (r (PowerSeries.coeff 0 f)) + TrivSqZeroExt.inr (r (PowerSeries.coeff 1 f))
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp [PowerSeries.coeff_one]
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, DualNumber.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, PowerSeries.coeff_mul,
        Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_insert,
        Finset.sum_singleton, map_add, map_mul, smul_eq_mul]
      simp
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by
    apply TrivSqZeroExt.ext <;> simp [add_add_add_comm]

theorem fst_rho {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) (f : PowerSeries O) :
    TrivSqZeroExt.fst (rho r f) = r (PowerSeries.constantCoeff f) := by
  show TrivSqZeroExt.fst (TrivSqZeroExt.inl (r (PowerSeries.coeff 0 f)) + TrivSqZeroExt.inr (r (PowerSeries.coeff 1 f))) = _
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

theorem snd_rho {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) (f : PowerSeries O) :
    TrivSqZeroExt.snd (rho r f) = r (PowerSeries.coeff 1 f) := by
  show TrivSqZeroExt.snd (TrivSqZeroExt.inl (r (PowerSeries.coeff 0 f)) + TrivSqZeroExt.inr (r (PowerSeries.coeff 1 f))) = _
  simp

theorem rho_C {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) (o : O) :
    rho r (PowerSeries.C o) = TrivSqZeroExt.inl (r o) := by
  apply TrivSqZeroExt.ext
  · rw [fst_rho, PowerSeries.constantCoeff_C, TrivSqZeroExt.fst_inl]
  · rw [snd_rho, PowerSeries.coeff_C, if_neg one_ne_zero, map_zero, TrivSqZeroExt.snd_inl]

theorem rho_X {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) :
    rho r (PowerSeries.X : PowerSeries O) = DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · rw [fst_rho, PowerSeries.constantCoeff_X, map_zero, DualNumber.fst_eps]
  · rw [snd_rho, PowerSeries.coeff_one_X, map_one, DualNumber.snd_eps]

section Cramer
variable {R : Type} [CommRing R]
open scoped Matrix
theorem funext_fin_two {X : Type} {f g : Fin 2 → X} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext i
  exact (Fin.forall_fin_two (p := fun i => f i = g i)).mpr ⟨h0, h1⟩ i

theorem existsUnique_coords (e₀ e₁ : Fin 2 → R) (δinv : R)
    (hδ : δinv * (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0) = 1) (m : Fin 2 → R) :
    ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁ := by
  refine ⟨(δinv * (m 0 * e₁ 1 - m 1 * e₁ 0), δinv * (e₀ 0 * m 1 - e₀ 1 * m 0)), ?_, ?_⟩
  · refine funext_fin_two ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 0)) * hδ
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 1)) * hδ
  · rintro ⟨c₁, c₂⟩ hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
    ext
    · simp only
      linear_combination (-c₁) * hδ - δinv * e₁ 1 * h0 + δinv * e₁ 0 * h1
    · simp only
      linear_combination (-c₂) * hδ + δinv * e₀ 1 * h0 - δinv * e₀ 0 * h1

end Cramer

universe u

section Homs
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)
variable {q : ℕ} [Fact q.Prime]

section homs

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A']

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

def castHom2 {A : Type u} [CommRing A] {X X' Y Y' : FormalODModule q A} (hX : X = X') (hY : Y = Y')
    (w : X.Hom Y) : X'.Hom Y' :=
  ⟨w.toSeries, by subst hX; subst hY; exact w.isODHom⟩

theorem castHom2_isIso {A : Type u} [CommRing A] {X X' Y Y' : FormalODModule q A} (hX : X = X') (hY : Y = Y')
    (w : X.Hom Y) (hw : w.IsIso) : (castHom2 hX hY w).IsIso := by
  subst hX; subst hY
  have : castHom2 rfl rfl w = w := FormalODModule.Hom.ext rfl
  rw [this]; exact hw
end Homs

end DDF4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_powerSeries_surjective_of_isProrepresentedBy_deformations_of_not_and.DDF4"

open DDF4 in
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
open scoped Matrix in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ χ : R →ₐ[Onr] PowerSeries Onr, Function.Surjective χ := by
  classical

  have hqmem : ((q : ℕ) : Onr) ∈ maximalIdeal Onr := by
    rw [← IsLocalRing.eq_maximalIdeal hOnr_max, ← map_natCast (algebraMap ℤ_[q] Onr) q]; exact Ideal.subset_span rfl
  haveI : IsAdicComplete (maximalIdeal Onr) Onr := by rwa [IsLocalRing.eq_maximalIdeal hOnr_max] at hOnr_complete
  have hqk : ((q : ℕ) : ResidueField Onr) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hqmem; rwa [map_natCast] at this
  haveI : CharP (ResidueField Onr) q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hqk
  haveI : IsAdicComplete (maximalIdeal (PowerSeries Onr)) (PowerSeries Onr) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := Onr)

  let resT : (PowerSeries Onr) →+* ResidueField Onr := (IsLocalRing.residue Onr).comp PowerSeries.constantCoeff
  have hresT : resT.comp (algebraMap Onr (PowerSeries Onr)) = IsLocalRing.residue Onr := by
    ext o; show IsLocalRing.residue Onr (PowerSeries.constantCoeff (algebraMap Onr (PowerSeries Onr) o)) = _
    rw [PowerSeries.algebraMap_eq, PowerSeries.constantCoeff_C]
  have hresT_surj : Function.Surjective resT := fun y => by
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Onr _ o, by rw [← RingHom.comp_apply, hresT]⟩

  obtain ⟨γ, hγ⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free q
    ((IsLocalRing.residue Onr).comp ι) X₀.toFormalODModule X₀.isSpecial inferInstance inferInstance
  obtain ⟨a, ha, h01⟩ := CerednikDrinfeld.FormalODModule.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis q
    ((IsLocalRing.residue Onr).comp ι) X₀.toFormalODModule γ hγ
  have hnotboth : ¬ (a 0 0 = 0 ∧ a 0 1 = 0) := by
    intro hb
    apply hsmooth

    have hL : ∀ i : Fin 2, MvFormalGroup.linearPart X₀.varpi *ᵥ MvFormalGroup.CartierModule.tangent (γ i) = 0 := by
      have hi : ∀ i : Fin 2, a 0 i = 0 := by rw [Fin.forall_fin_two]; exact ⟨hb.1, hb.2⟩
      intro i
      have h := CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants q
        X₀.toFormalODModule γ a ha i
      rw [h, hi, zero_smul]
    have hzero : MvFormalGroup.linearPart X₀.varpi = 0 := by

      have hdet : IsUnit (MvFormalGroup.CartierModule.tangent (γ 0) 0 * MvFormalGroup.CartierModule.tangent (γ 1) 1 -
          MvFormalGroup.CartierModule.tangent (γ 0) 1 * MvFormalGroup.CartierModule.tangent (γ 1) 0) := by
        have h := hγ.2; rw [Matrix.det_fin_two] at h; exact h
      obtain ⟨δ, hδ⟩ := hdet.exists_left_inv
      ext i k
      obtain ⟨⟨c₁, c₂⟩, hc, -⟩ := DDF4.existsUnique_coords _ _ δ hδ (Pi.single k (1 : ResidueField Onr))
      have : MvFormalGroup.linearPart X₀.varpi *ᵥ (Pi.single k 1) = 0 := by
        rw [hc, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hL 0, hL 1, smul_zero, smul_zero, add_zero]
      have := congrFun this i
      simpa [Matrix.mulVec_single_one] using this
    constructor <;> intro m _ <;> rw [Matrix.mulVecLin_apply, hzero, Matrix.zero_mulVec]
  have hone : a 0 0 = 0 ∨ a 0 1 = 0 := by
    rcases mul_eq_zero.mp (h01.trans hqk) with h | h
    exacts [Or.inl h, Or.inr h]

  obtain ⟨δa, hδa0, hversal⟩ := CerednikDrinfeld.SpecialFormalODModule.exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and X₀ hsmooth γ hγ a ha h01

  let lift : ResidueField Onr → Onr := fun x => (IsLocalRing.residue_surjective x).choose
  have hlift : ∀ x, IsLocalRing.residue Onr (lift x) = x := fun x => (IsLocalRing.residue_surjective x).choose_spec

  have hunit_lift : ∀ x : ResidueField Onr, x ≠ 0 → IsUnit (lift x) := by
    intro x hx
    by_contra hnu
    apply hx
    rw [← hlift x]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hnu
  let uidx : Fin 2 := if a 0 0 = 0 then 1 else 0
  have hune : a 0 uidx ≠ 0 := by
    by_cases h : a 0 0 = 0
    · simp only [uidx, if_pos h]; exact fun h1 => hnotboth ⟨h, h1⟩
    · simp only [uidx, if_neg h]; exact h
  obtain ⟨uu0, huu0⟩ := (hunit_lift _ hune)

  let a' : ℕ → Fin 2 → (PowerSeries Onr) := fun m i =>
    if m = 0 then (if i = uidx then PowerSeries.C (uu0 : Onr) else PowerSeries.C (((q : ℕ) : Onr) * (uu0⁻¹ : Onrˣ)))
    else PowerSeries.C (lift (a m i)) + PowerSeries.C (lift (δa m i)) * PowerSeries.X
  have ha'slot : ∀ m i, rho (IsLocalRing.residue Onr) (a' m i) =
      algebraMap (ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr)) (a m i) + δa m i • DualNumber.eps := by
    intro m i
    by_cases hm : m = 0
    · subst hm
      rw [hδa0 i, zero_smul, add_zero]
      simp only [a', if_true]
      by_cases hi : i = uidx
      · rw [if_pos hi, rho_C, huu0, hlift, hi]; rfl
      · rw [if_neg hi, rho_C, map_mul, map_natCast, hqk, zero_mul]
        have : a 0 i = 0 := by
          by_cases h0 : a 0 0 = 0
          · have : uidx = 1 := by simp only [uidx, if_pos h0]
            fin_cases i
            · exact h0
            · exact absurd (this ▸ rfl) hi
          · have : uidx = 0 := by simp only [uidx, if_neg h0]
            fin_cases i
            · exact absurd (this ▸ rfl) hi
            · exact hone.resolve_left h0
        rw [this, map_zero]; rfl
    · simp only [a', if_neg hm, map_add, map_mul, rho_C, rho_X, hlift]
      congr 1
      rw [TrivSqZeroExt.inl_mul_eq_smul]
  have ha' : ∀ m i, resT (a' m i) = a m i := by
    intro m i
    have h := congrArg TrivSqZeroExt.fst (ha'slot m i)
    rw [fst_rho, TrivSqZeroExt.fst_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl] at h
    rw [TrivSqZeroExt.fst_smul, DualNumber.fst_eps, smul_zero, add_zero] at h
    exact h
  have h01' : a' 0 0 * a' 0 1 = ((q : ℕ) : (PowerSeries Onr)) := by
    have hu : (uu0 : Onr) * (((q : ℕ) : Onr) * (uu0⁻¹ : Onrˣ)) = (q : ℕ) := by
      rw [mul_comm, mul_assoc, Units.inv_mul, mul_one]
    simp only [a', if_true]
    by_cases h0 : a 0 0 = 0
    · have : uidx = 1 := by simp only [uidx, if_pos h0]
      rw [this, if_neg (show (0 : Fin 2) ≠ 1 by decide), if_pos rfl, ← map_mul, mul_comm, hu, map_natCast]
    · have : uidx = 0 := by simp only [uidx, if_neg h0]
      rw [this, if_pos rfl, if_neg (show (1 : Fin 2) ≠ 0 by decide), ← map_mul, hu, map_natCast]

  have hsep : IsHausdorff (Ideal.span {((q : ℕ) : ResidueField Onr)}) (ResidueField Onr) := by
    rw [hqk, Ideal.span_singleton_zero]; infer_instance
  have hjT : resT.comp ((algebraMap Onr (PowerSeries Onr)).comp ι) = (IsLocalRing.residue Onr).comp ι := by
    rw [← RingHom.comp_assoc, hresT]
  have hγ' : X₀.toFormalODModule.IsHomogeneousVBasis (resT.comp ((algebraMap Onr (PowerSeries Onr)).comp ι)) γ := by rw [hjT]; exact hγ
  obtain ⟨X', γl, hγl, hal, u, hu, hγlred⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
      q ((algebraMap Onr (PowerSeries Onr)).comp ι) resT hsep X₀.toFormalODModule γ hγ' a ha a' ha' h01'

  obtain ⟨χ, hχres, hχn⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
      Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO (PowerSeries Onr) resT hresT_surj hresT X' u hu
  have hsurjR : Function.Surjective resR := by
    intro y; obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩
  have hkerR : RingHom.ker resR = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR hsurjR)
  have hkerT : RingHom.ker resT = maximalIdeal (PowerSeries Onr) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resT hresT_surj)

  refine ⟨χ, IsLocalRing.surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq χ.toRingHom ?_ ?_ ?_⟩
  · intro r hr
    rw [← hkerT, RingHom.mem_ker]
    rw [← hkerR, RingHom.mem_ker] at hr
    change (resT.comp χ.toRingHom) r = 0
    rw [hχres]; exact hr
  · intro s
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (resT s)
    refine ⟨algebraMap Onr R o, ?_⟩
    rw [← hkerT, RingHom.mem_ker, map_sub, sub_eq_zero]
    change resT s = resT (χ (algebraMap Onr R o))
    rw [AlgHom.commutes, ← RingHom.comp_apply, hresT]
    exact ho.symm
  ·

    have hq_R : algebraMap Onr R ((q : ℕ) : Onr) ∈ maximalIdeal R := by
      rw [← hkerR, RingHom.mem_ker, ← RingHom.comp_apply, hresR]; exact (IsLocalRing.residue_eq_zero_iff _).mpr hqmem
    have hCq : (PowerSeries.C ((q : ℕ) : Onr) : (PowerSeries Onr)) ∈ (maximalIdeal R).map χ.toRingHom := by
      have : (PowerSeries.C ((q : ℕ) : Onr) : (PowerSeries Onr)) = χ (algebraMap Onr R ((q : ℕ) : Onr)) := by
        rw [AlgHom.commutes, PowerSeries.algebraMap_eq]
      rw [this]; exact Ideal.mem_map_of_mem _ hq_R
    have hmax : maximalIdeal Onr = Ideal.span {((q : ℕ) : Onr)} := by
      rw [← IsLocalRing.eq_maximalIdeal hOnr_max, map_natCast]

    suffices hX : (PowerSeries.X : (PowerSeries Onr)) ∈ (maximalIdeal R).map χ.toRingHom ⊔ maximalIdeal (PowerSeries Onr) ^ 2 by
      intro f hf
      have hf₀ : PowerSeries.constantCoeff f ∈ maximalIdeal Onr := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
        exact fun hu => hf (PowerSeries.isUnit_iff_constantCoeff.mpr hu)
      rw [hmax, Ideal.mem_span_singleton] at hf₀
      obtain ⟨c, hc⟩ := hf₀
      rw [PowerSeries.eq_X_mul_shift_add_const f, hc, map_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hX) (Ideal.mul_mem_right _ _ (Ideal.mem_sup_left hCq))
    have hXmem : (PowerSeries.X : (PowerSeries Onr)) ∈ maximalIdeal (PowerSeries Onr) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
      exact not_isUnit_zero

    have hfstρχ : ∀ x : R, TrivSqZeroExt.fst ((rho (IsLocalRing.residue Onr)) (χ x)) = resR x := fun x => by
      rw [fst_rho]; change (resT.comp χ.toRingHom) x = resR x; rw [hχres]
    by_cases hcase : ∃ x ∈ maximalIdeal R, TrivSqZeroExt.snd ((rho (IsLocalRing.residue Onr)) (χ x)) ≠ 0
    ·
      obtain ⟨x, hx, hne⟩ := hcase
      have h0 : PowerSeries.constantCoeff (χ x) ∈ maximalIdeal Onr := by
        have := hfstρχ x
        rw [fst_rho, show resR x = 0 from by rw [← hkerR] at hx; exact hx] at this
        exact (IsLocalRing.residue_eq_zero_iff _).mp this
      rw [hmax, Ideal.mem_span_singleton] at h0
      obtain ⟨c₀, hc₀⟩ := h0
      have h1 : IsUnit (PowerSeries.coeff 1 (χ x)) := by
        by_contra hnu
        apply hne
        rw [snd_rho]; exact (IsLocalRing.residue_eq_zero_iff _).mpr hnu
      obtain ⟨c₁, hc₁⟩ := h1.exists_left_inv

      obtain ⟨g₁, hg₁⟩ : ∃ g, g = PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (χ x) := ⟨_, rfl⟩
      obtain ⟨g₂, hg₂⟩ : ∃ g, g = PowerSeries.mk fun p => PowerSeries.coeff (p + 1) g₁ := ⟨_, rfl⟩
      have hdec₁ : g₁ = PowerSeries.X * g₂ + PowerSeries.C (PowerSeries.coeff 1 (χ x)) := by
        have := PowerSeries.eq_X_mul_shift_add_const g₁
        rw [← hg₂, show PowerSeries.constantCoeff g₁ = PowerSeries.coeff 1 (χ x) by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg₁, PowerSeries.coeff_mk]] at this
        exact this
      have hdec : χ x = PowerSeries.X * (PowerSeries.X * g₂ + PowerSeries.C (PowerSeries.coeff 1 (χ x))) +
          PowerSeries.C (((q : ℕ) : Onr) * c₀) := by
        have := PowerSeries.eq_X_mul_shift_add_const (χ x)
        rw [← hg₁, hdec₁, hc₀] at this
        exact this

      have hXeq : (PowerSeries.X : (PowerSeries Onr)) = PowerSeries.C c₁ * (χ x - PowerSeries.C (((q : ℕ) : Onr) * c₀) -
          PowerSeries.X * PowerSeries.X * g₂) := by
        have e : χ x - PowerSeries.C (((q : ℕ) : Onr) * c₀) - PowerSeries.X * PowerSeries.X * g₂
            = PowerSeries.X * PowerSeries.C (PowerSeries.coeff 1 (χ x)) := by
          conv_lhs => rw [hdec]
          ring
        rw [e, ← mul_assoc, mul_comm (PowerSeries.C c₁) PowerSeries.X, mul_assoc, ← map_mul, hc₁, map_one, mul_one]
      rw [hXeq]
      refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx))
        (Ideal.mem_sup_left ?_)) (Ideal.mem_sup_right ?_))
      · rw [map_mul]; exact Ideal.mul_mem_right _ _ hCq
      · rw [pow_two]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hXmem hXmem)
    ·
      exfalso
      push Not at hcase
      have hρχ : (rho (IsLocalRing.residue Onr)).comp χ.toRingHom = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp resR := by
        refine RingHom.ext fun r => ?_
        obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (resR r)
        have hx : r - algebraMap Onr R o ∈ maximalIdeal R := by
          rw [← hkerR, RingHom.mem_ker, map_sub, sub_eq_zero, ← RingHom.comp_apply, hresR]; exact ho.symm
        have hz : (rho (IsLocalRing.residue Onr)) (χ (r - algebraMap Onr R o)) = 0 := by
          apply TrivSqZeroExt.ext
          · rw [hfstρχ, TrivSqZeroExt.fst_zero]; rw [← hkerR] at hx; exact hx
          · rw [hcase _ hx, TrivSqZeroExt.snd_zero]
        rw [map_sub, map_sub, sub_eq_zero, AlgHom.commutes, PowerSeries.algebraMap_eq, rho_C] at hz
        change (rho (IsLocalRing.residue Onr)) (χ r) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))) (resR r)
        rw [hz, ← ho, TrivSqZeroExt.algebraMap_eq_inl]

      have hfstρ : ∀ f ∈ maximalIdeal (PowerSeries Onr), TrivSqZeroExt.fst ((rho (IsLocalRing.residue Onr)) f) = 0 := by
        intro f hf
        rw [fst_rho, IsLocalRing.residue_eq_zero_iff]
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
        exact fun hu => hf (PowerSeries.isUnit_iff_constantCoeff.mpr hu)
      have hker2 : ∀ f ∈ maximalIdeal (PowerSeries Onr) ^ 2, (rho (IsLocalRing.residue Onr)) f = 0 := by
        intro f hf
        rw [← RingHom.mem_ker]
        refine (show maximalIdeal (PowerSeries Onr) ^ 2 ≤ RingHom.ker (rho (IsLocalRing.residue Onr)) from ?_) hf
        rw [pow_two, Ideal.mul_le]
        intro f hf g hg
        rw [RingHom.mem_ker, map_mul]
        apply TrivSqZeroExt.ext
        · rw [TrivSqZeroExt.fst_mul, hfstρ f hf, zero_mul, TrivSqZeroExt.fst_zero]
        · rw [DualNumber.snd_mul, hfstρ f hf, hfstρ g hg, zero_mul, mul_zero, add_zero, TrivSqZeroExt.snd_zero]
      let ρ2 : (PowerSeries Onr) ⧸ maximalIdeal (PowerSeries Onr) ^ 2 →+* (DualNumber (IsLocalRing.ResidueField Onr)) :=
        Ideal.Quotient.lift (maximalIdeal (PowerSeries Onr) ^ 2) (rho (IsLocalRing.residue Onr)) hker2
      have hρ2 : ρ2.comp (Ideal.Quotient.mk (maximalIdeal (PowerSeries Onr) ^ 2)) = (rho (IsLocalRing.residue Onr)) := RingHom.ext fun _ => rfl

      obtain ⟨v, hv, -⟩ := hχn 2 two_pos
      have hsrc : (Xu.map ((Ideal.Quotient.mk (maximalIdeal (PowerSeries Onr) ^ 2)).comp χ.toRingHom)).map ρ2 = (Xu.map resR).map (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))) := by
        rw [FormalODModule.map_map, FormalODModule.map_map, ← RingHom.comp_assoc, hρ2, hρχ]
      have htgt : (X'.map (Ideal.Quotient.mk (maximalIdeal (PowerSeries Onr) ^ 2))).map ρ2 = X'.map (rho (IsLocalRing.residue Onr)) := by
        rw [FormalODModule.map_map, hρ2]
      obtain ⟨g₁, hg₁, hg₂⟩ := exists_inv (castHom2_isIso hsrc htgt (v.map ρ2) (isIso_map ρ2 hv))
      have hg₁iso : g₁.IsIso := ⟨castHom2 hsrc htgt (v.map ρ2), FormalODModule.Hom.ext hg₂, FormalODModule.Hom.ext hg₁⟩
      have hθ : ((wu.map (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr)))).comp g₁).IsIso := isIso_comp (isIso_map _ hwu) hg₁iso

      have hγρ := hγl.map (rho (IsLocalRing.residue Onr))
      have haρ := hal.map (rho (IsLocalRing.residue Onr))
      obtain ⟨hγ'', ha''⟩ :=
        CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso q
          ((rho (IsLocalRing.residue Onr)).comp ((algebraMap Onr (PowerSeries Onr)).comp ι)) _ _ ((wu.map (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr)))).comp g₁) hθ _ hγρ _ haρ
      have hj : (rho (IsLocalRing.residue Onr)).comp ((algebraMap Onr (PowerSeries Onr)).comp ι) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp ((IsLocalRing.residue Onr).comp ι) := by
        refine RingHom.ext fun z => ?_
        simp only [RingHom.comp_apply]
        rw [PowerSeries.algebraMap_eq, rho_C, TrivSqZeroExt.algebraMap_eq_inl]
      have hconst : (fun m i => (rho (IsLocalRing.residue Onr)) (a' m i)) =
          (fun m i => (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))) (a m i) + δa m i • DualNumber.eps) := by
        funext m i; rw [ha'slot]
      rw [hj] at hγ''
      rw [hconst] at ha''
      exact hversal _ hγ'' ha''

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_powerSeries_surjective_of_isProrepresentedBy_deformations_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_powerSeries_surjective_of_isProrepresentedBy_deformations_of_not_and (solution)
