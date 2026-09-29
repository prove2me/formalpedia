-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7b0dc509-3560-5a3c-a4d1-d022b2349443

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations_of_forall_bijective_algHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_of_charP
import Theorems.Thm_MvFormalGroup_charP_of_finrank_quotient_span_nthSeries_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

noncomputable section

namespace R4D1ProrepSkeleton

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule IsLocalRing
open MvPowerSeries (constantCoeff)

variable {q : ℕ} [Fact q.Prime]

section homs

variable {A : Type} [CommRing A] {A' : Type} [CommRing A']

theorem cc_map {φ : Series A} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : A →+* A') (i : Fin 2) :
    constantCoeff ((φ.map f) i) = 0 := by
  show constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ i, map_zero]

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

theorem isIso_symm {f : X.Hom Y} {g : Y.Hom X} (h₁ : g.comp f = FormalODModule.Hom.id X)
    (h₂ : f.comp g = FormalODModule.Hom.id Y) : g.IsIso :=
  ⟨f, h₂, h₁⟩

theorem isIso_comp {g : Y.Hom Z} {f : X.Hom Y} (hg : g.IsIso) (hf : f.IsIso) : (g.comp f).IsIso := by
  obtain ⟨g', hg'₁, hg'₂⟩ := hg
  obtain ⟨f', hf'₁, hf'₂⟩ := hf
  refine ⟨f'.comp g', FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩
  · have e1 := congrArg FormalODModule.Hom.toSeries hg'₁
    have e2 := congrArg FormalODModule.Hom.toSeries hf'₁
    simp only [comp_toSeries, id_toSeries] at e1 e2 ⊢
    rw [Series.comp_assoc _ _ _ (hom_cc g') (Series.constantCoeff_comp (hom_cc g) (hom_cc f)),
      ← Series.comp_assoc _ _ _ (hom_cc g) (hom_cc f), e1, Series.id_comp _ (hom_cc f), e2]
  · have e1 := congrArg FormalODModule.Hom.toSeries hg'₂
    have e2 := congrArg FormalODModule.Hom.toSeries hf'₂
    simp only [comp_toSeries, id_toSeries] at e1 e2 ⊢
    rw [Series.comp_assoc _ _ _ (hom_cc f) (Series.constantCoeff_comp (hom_cc f') (hom_cc g')),
      ← Series.comp_assoc _ _ _ (hom_cc f') (hom_cc g'), e2, Series.id_comp _ (hom_cc g'), e1]

theorem isIso_map (r : A →+* A') {f : X.Hom Y} (hf : f.IsIso) : (f.map r).IsIso := by
  obtain ⟨g, hg₁, hg₂⟩ := hf
  refine ⟨g.map r, FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩
  · have e1 := congrArg FormalODModule.Hom.toSeries hg₁
    simp only [comp_toSeries, id_toSeries, map_toSeries] at e1 ⊢
    rw [← Series.map_comp r _ _ (hom_cc f), e1, Series.map_id]
  · have e2 := congrArg FormalODModule.Hom.toSeries hg₂
    simp only [comp_toSeries, id_toSeries, map_toSeries] at e2 ⊢
    rw [← Series.map_comp r _ _ (hom_cc g), e2, Series.map_id]

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

theorem isIso_of_toSeries_eq {X X' : FormalODModule q A} (h : X = X') {Y : FormalODModule q A}
    (w : X.Hom Y) (hw : w.IsIso) (w' : X'.Hom Y) (hww' : w'.toSeries = w.toSeries) : w'.IsIso := by
  have : w' = castHom h w := FormalODModule.Hom.ext hww'
  rw [this]
  exact castHom_isIso h w hw

theorem exists_isIso_of_eq {X X' : FormalODModule q A} (h : X = X') :
    ∃ v : X.Hom X', v.IsIso ∧ v.toSeries = Series.id A := by
  subst h
  exact ⟨FormalODModule.Hom.id X, id_isIso X, rfl⟩

end homs

section pairs

variable {k : Type} [Field k] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

structure Pair (A : Type) [CommRing A] (res : A →+* k) where

  X : FormalODModule q A

  w : (X.map res).Hom X₀.toFormalODModule

  hw : w.IsIso

variable {X₀}

def Rel {A : Type} [CommRing A] {res : A →+* k} (P Q : Pair X₀ A res) : Prop :=
  ∃ v : P.X.Hom Q.X, v.IsIso ∧ Q.w.toSeries.comp (v.toSeries.map res) = P.w.toSeries

variable {A : Type} [CommRing A] {res : A →+* k}

theorem rel_of_isIso_of_id {P Q : Pair X₀ A res} (v : P.X.Hom Q.X) (hv : v.IsIso)
    (hvid : v.toSeries = Series.id A) (hw : Q.w.toSeries = P.w.toSeries) : Rel P Q := by
  refine ⟨v, hv, ?_⟩
  rw [hvid, Series.map_id, Series.comp_id, hw]

theorem rel_refl (P : Pair X₀ A res) : Rel P P :=
  rel_of_isIso_of_id (FormalODModule.Hom.id P.X) (id_isIso _) rfl rfl

theorem rel_symm {P Q : Pair X₀ A res} (h : Rel P Q) : Rel Q P := by
  obtain ⟨v, ⟨g, hg₁, hg₂⟩, hc⟩ := h
  refine ⟨g, ⟨v, hg₂, hg₁⟩, ?_⟩
  have e2 := congrArg FormalODModule.Hom.toSeries hg₂
  simp only [comp_toSeries, id_toSeries] at e2
  rw [← hc, Series.comp_assoc _ _ _ (cc_map (hom_cc v) res) (cc_map (hom_cc g) res),
    ← Series.map_comp res _ _ (hom_cc g), e2, Series.map_id, Series.comp_id]

theorem rel_trans {P Q S : Pair X₀ A res} (h₁ : Rel P Q) (h₂ : Rel Q S) : Rel P S := by
  obtain ⟨v₁, hv₁, hc₁⟩ := h₁
  obtain ⟨v₂, hv₂, hc₂⟩ := h₂
  refine ⟨v₂.comp v₁, isIso_comp hv₂ hv₁, ?_⟩
  rw [comp_toSeries, Series.map_comp res _ _ (hom_cc v₁),
    ← Series.comp_assoc _ _ _ (cc_map (hom_cc v₂) res) (cc_map (hom_cc v₁) res), hc₂, hc₁]

def Pair.mapPair {A' : Type} [CommRing A'] {res' : A' →+* k} (f : A →+* A') (hf : res'.comp f = res)
    (P : Pair X₀ A res) : Pair X₀ A' res' where
  X := P.X.map f
  w := castHom (by rw [FormalODModule.map_map, hf]) P.w
  hw := castHom_isIso _ P.w P.hw

@[scoped simp] theorem Pair.mapPair_X {A' : Type} [CommRing A'] {res' : A' →+* k} (f : A →+* A')
    (hf : res'.comp f = res) (P : Pair X₀ A res) : (P.mapPair f hf).X = P.X.map f := rfl

p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton.Pair"
@[scoped simp] theorem Pair.mapPair_w_toSeries {A' : Type} [CommRing A'] {res' : A' →+* k} (f : A →+* A')
    (hf : res'.comp f = res) (P : Pair X₀ A res) : (P.mapPair f hf).w.toSeries = P.w.toSeries := rfl

p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton.Pair"
theorem rel_mapPair {A' : Type} [CommRing A'] {res' : A' →+* k} (f : A →+* A')
    (hf : res'.comp f = res) {P Q : Pair X₀ A res} (h : Rel P Q) :
    Rel (P.mapPair f hf) (Q.mapPair f hf) := by
  obtain ⟨v, hv, hc⟩ := h
  refine ⟨v.map f, isIso_map f hv, ?_⟩
  simp only [Pair.mapPair_w_toSeries, Pair.mapPair_X, map_toSeries]
  rw [Series.map_map, hf, hc]

theorem rel_mapPair_id (P : Pair X₀ A res) (h : res.comp (RingHom.id A) = res) :
    Rel (P.mapPair (RingHom.id A) h) P := by
  obtain ⟨v, hv, hvid⟩ := exists_isIso_of_eq (X := (P.mapPair (RingHom.id A) h).X) (X' := P.X)
    (by simp)
  exact rel_of_isIso_of_id v hv hvid rfl

theorem rel_mapPair_comp {A' : Type} [CommRing A'] {res' : A' →+* k} {A'' : Type} [CommRing A'']
    {res'' : A'' →+* k} (f : A →+* A') (g : A' →+* A'') (hf : res'.comp f = res)
    (hg : res''.comp g = res') (hgf : res''.comp (g.comp f) = res) (P : Pair X₀ A res) :
    Rel (P.mapPair (g.comp f) hgf) ((P.mapPair f hf).mapPair g hg) := by
  obtain ⟨v, hv, hvid⟩ := exists_isIso_of_eq (X := (P.mapPair (g.comp f) hgf).X)
    (X' := ((P.mapPair f hf).mapPair g hg).X) (by simp [FormalODModule.map_map])
  exact rel_of_isIso_of_id v hv hvid rfl

def basePair : Pair X₀ k (RingHom.id k) where
  X := X₀.toFormalODModule
  w := castHom (FormalODModule.map_id _).symm (FormalODModule.Hom.id _)
  hw := castHom_isIso _ _ (id_isIso _)

theorem rel_basePair (P : Pair X₀ k (RingHom.id k)) : Rel P (basePair (X₀ := X₀)) := by
  refine ⟨castHom (FormalODModule.map_id _) P.w, castHom_isIso _ _ P.hw, ?_⟩
  show (Series.id k).comp (P.w.toSeries.map (RingHom.id k)) = P.w.toSeries
  rw [Series.map_ringHom_id, Series.id_comp _ (hom_cc P.w)]

end pairs
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton.Pair"

section localfacts

variable {k : Type} [Field k]

theorem isLocalHom_of_comp_eq {A'' A : Type} [CommRing A''] [CommRing A] [IsLocalRing A'']
    (res'' : A'' →+* k) (hs'' : Function.Surjective res'') (res : A →+* k)
    (hres : ∀ a : A, IsUnit a → res a ≠ 0) (f : A'' →+* A) (hf : res.comp f = res'') :
    IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ IsLocalRing.maximalIdeal A'' := hna
  have hker : RingHom.ker res'' = IsLocalRing.maximalIdeal A'' :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective res'' hs'')
  have h0 : res'' a = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact hmem
  have h1 : res (f a) ≠ 0 := hres (f a) ha
  apply h1
  have := congrArg (fun g => g a) hf
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [this, h0]

theorem res_ne_zero_of_isUnit {A : Type} [CommRing A] [IsLocalRing A] (res : A →+* k)
    (hs : Function.Surjective res) (a : A) (ha : IsUnit a) : res a ≠ 0 := by
  intro h0
  have hker : RingHom.ker res = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective res hs)
  have hmem : a ∈ IsLocalRing.maximalIdeal A := by
    rw [← hker, RingHom.mem_ker]
    exact h0
  exact (IsLocalRing.mem_maximalIdeal a).mp hmem ha

theorem isNilpotent_ker {A : Type} [CommRing A] [IsLocalRing A] [IsArtinianRing A] (res : A →+* k)
    (hs : Function.Surjective res) : IsNilpotent (RingHom.ker res) := by
  have hker : RingHom.ker res = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective res hs)
  rw [hker]
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹_›

end localfacts
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton.Pair"

theorem charP_of_specialFormalODModule {k : Type} [Field k] {j₀ : Zp2 q →+* k}
    (X₀ : SpecialFormalODModule q j₀) : CharP k q := by
  obtain ⟨-, -, hrank⟩ := X₀.hasHeight
  have h := hrank k (RingHom.id k)
  rw [Series.map_ringHom_id, FormalODModule.act_natCast] at h
  exact MvFormalGroup.charP_of_finrank_quotient_span_nthSeries_eq_pow q X₀.F 4 h (by norm_num)

end R4D1ProrepSkeleton
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton.Pair P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton.Pair P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations.R4D1ProrepSkeleton"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal IsLocalRing R4D1ProrepSkeleton in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (ι : CerednikDrinfeld.Zp2 q →+* O)
    (X₀ : CerednikDrinfeld.SpecialFormalODModule q ((IsLocalRing.residue O).comp ι)) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : Algebra O R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
      (resR : R →+* IsLocalRing.ResidueField O) (_ : resR.comp (algebraMap O R) = IsLocalRing.residue O)
      (Xu : CerednikDrinfeld.FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule)
      (_ : wu.IsIso),
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
            (resA : A →+* IsLocalRing.ResidueField O), Function.Surjective resA →
            resA.comp (algebraMap O A) = IsLocalRing.residue O →
          ∀ (X : CerednikDrinfeld.FormalODModule q A), X.IsSpecial ((algebraMap O A).comp ι) →
            X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries) := by
  classical
  haveI hchar : CharP (ResidueField O) q := charP_of_specialFormalODModule X₀

  obtain ⟨r, e, he_iso, he_inj, he_smul, he_add⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_of_charP X₀

  obtain ⟨R, i1, i2, i3, i4, i5, resR, hresR, β, hβ_res, hβ_rel, hβ_nat, hβ_inj, hβ_surj⟩ :=
    IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective O
      (fun A _ _ resA => Pair X₀ A resA)
      (fun P Q => Rel P Q)
      (fun P => rel_refl P)
      (fun P Q h => rel_symm h)
      (fun P Q S h₁ h₂ => rel_trans h₁ h₂)
      (fun f hf P => P.mapPair f.toRingHom hf)
      (fun f hf P Q h => rel_mapPair f.toRingHom hf h)
      (fun h P => rel_mapPair_id P h)
      (fun f g hf hg hgf P => rel_mapPair_comp f.toRingHom g.toRingHom hf hg hgf P)
      basePair
      (fun P => rel_basePair P)
      (by
        intro B _ _ _ _ resB hsB hcB A' _ _ _ _ resA' hsA' hcA' A'' _ _ _ _ resA'' hsA'' hcA''
          A _ _ _ _ resA hsA hcA p' hp' p'' hp'' q' hq' q'' hq'' hcomm hpb hq''s
        have hloc : IsLocalHom q''.toRingHom :=
          isLocalHom_of_comp_eq resA'' hsA'' resA (res_ne_zero_of_isUnit resA hsA) q''.toRingHom hq''
        obtain ⟨hex, huniq⟩ :=
          CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective
            X₀ p'.toRingHom p''.toRingHom q'.toRingHom q''.toRingHom
            (congrArg AlgHom.toRingHom hcomm) (fun a' a'' h => hpb a' a'' h) hq''s hloc
            resB resA' resA'' resA hp' hp'' hq' hq'' hsA (isNilpotent_ker resA hsA)
        refine ⟨?_, ?_⟩
        · intro P' P'' hrel
          obtain ⟨φ, hφ, hcφ⟩ := hrel
          obtain ⟨Y, u, hu, hYp', huw', v, hv, -, hcv⟩ :=
            hex P'.X P'.w P'.hw P''.X P''.w P''.hw φ hφ hcφ
          refine ⟨⟨Y, u, hu⟩, ?_, ⟨v, hv, hcv⟩⟩
          obtain ⟨v₁, hv₁, hv₁id⟩ := exists_isIso_of_eq (X := (Pair.mapPair p'.toRingHom hp'
            (⟨Y, u, hu⟩ : Pair X₀ B resB)).X) (X' := P'.X) hYp'
          exact rel_of_isIso_of_id v₁ hv₁ hv₁id huw'.symm
        · intro P₁ P₂ h' h''
          obtain ⟨v', hv', hc'⟩ := h'
          obtain ⟨v'', hv'', hc''⟩ := h''
          obtain ⟨v, hv, -, -, hc⟩ :=
            huniq P₁.X P₁.w P₁.hw P₂.X P₂.w P₂.hw v' hv' hc' v'' hv'' hc''
          exact ⟨v, hv, hc⟩)
      r
      (fun P => e P.X P.w P.hw)
      (fun P Q h => by
        obtain ⟨v, hv, hc⟩ := h
        exact he_iso P.X P.w P.hw Q.X Q.w Q.hw v hv hc)
      (fun P Q h => he_inj P.X P.w P.hw Q.X Q.w Q.hw h)
      (fun c μ hμ hsnd P => he_smul c μ.toRingHom hμ hsnd P.X P.w P.hw _ _ rfl)
      (by
        intro B _ _ _ _ resB hsB hcB p₁ p₂ σ hp₁ hp₂ hσ _ _ hsndσ P
        have hloc : IsLocalHom resB :=
          isLocalHom_of_comp_eq resB hsB (RingHom.id _) (fun a ha => by simpa using ha.ne_zero)
            resB (RingHom.id_comp _)
        exact he_add B resB hsB hloc p₁.toRingHom p₂.toRingHom σ.toRingHom hp₁ hp₂ hσ hsndσ
          P.X P.w P.hw _ _ _ _ _ _ rfl rfl rfl)

  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  obtain ⟨Xu, wu, hwu, hPRO⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations_of_forall_bijective_algHom
      O ι X₀ R resR hresR
      (fun A _ _ _ _ resA hs hc X w hw => β A resA hs hc ⟨X, w, hw⟩)
      (fun A _ _ _ _ resA hs hc X w hw => hβ_res A resA hs hc ⟨X, w, hw⟩)
      (fun A _ _ _ _ resA hs hc X w hw X' w' hw' v hv hcv =>
        hβ_rel A resA hs hc ⟨X, w, hw⟩ ⟨X', w', hw'⟩ ⟨v, hv, hcv⟩)
      (by
        intro A _ _ _ _ resA hs hc A' _ _ _ _ resA' hs' hc' f hf X w hw w' hw' hww'
        have key := hβ_nat A resA hs hc A' resA' hs' hc' f hf ⟨X, w, hw⟩
        have hP : (Pair.mapPair (X₀ := X₀) f.toRingHom hf ⟨X, w, hw⟩) = ⟨X.map f.toRingHom, w', hw'⟩ := by
          have hw'eq : w' = (Pair.mapPair (X₀ := X₀) f.toRingHom hf ⟨X, w, hw⟩).w :=
            FormalODModule.Hom.ext hww'
          subst hw'eq
          rfl
        rw [hP] at key
        exact key)
      (fun A _ _ _ _ resA hs hc X w hw X' w' hw' h => hβ_inj A resA hs hc ⟨X, w, hw⟩ ⟨X', w', hw'⟩ h)
      (fun A _ _ _ _ resA hs hc χ hχ => by
        obtain ⟨P, hP⟩ := hβ_surj A resA hs hc χ hχ
        exact ⟨P.X, P.w, P.hw, hP⟩)
  exact ⟨R, i1, i2, i3, i4, i5, resR, hresR, Xu, wu, hwu,
    fun A _ _ _ _ resA hs hc X _ _ w hw => hPRO A resA hs hc X w hw⟩

end S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations (solution)
