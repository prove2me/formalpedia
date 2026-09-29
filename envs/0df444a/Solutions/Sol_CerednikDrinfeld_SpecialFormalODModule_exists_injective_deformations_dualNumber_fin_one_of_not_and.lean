-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_fin_one_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5b4ef3ae-5c41-56fb-b4fe-b64caccac77d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
import Theorems.Thm_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
import Theorems.Thm_MvFormalGroup_Hom_eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow
import Theorems.Thm_MvFormalGroup_translate_injective_and_exists_hom_iff_exists_addCoboundary
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

noncomputable section

namespace F2aLine

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

section dual

variable (k : Type u) [Field k]

abbrev resD : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

theorem resD_surjective : Function.Surjective (resD k) := fun a =>
  ⟨TrivSqZeroExt.inl a, rfl⟩

theorem isLocalHom_resD : IsLocalHom (resD k) := by
  refine ⟨fun x hx => ?_⟩
  exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hx

theorem ker_resD_sq : RingHom.ker (resD k) ^ (1 + 1) = ⊥ := by
  rw [pow_succ, pow_one, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  change TrivSqZeroExt.fst r = 0 at hr
  change TrivSqZeroExt.fst s = 0 at hs
  rw [Ideal.mem_bot]
  refine TrivSqZeroExt.ext ?_ ?_
  · change TrivSqZeroExt.fst (r * s) = 0
    rw [TrivSqZeroExt.fst_mul, hr, zero_mul]
  · change TrivSqZeroExt.snd (r * s) = 0
    rw [DualNumber.snd_mul, hr, hs, zero_mul, mul_zero, add_zero]

theorem resD_comp_inl : (resD k).comp (TrivSqZeroExt.inlHom k k) = RingHom.id k := RingHom.ext fun _ => rfl

variable {k}

section cocycles

variable {n : ℕ} {F₀ : MvFormalGroup n k}

theorem isSymmTwoCocycle_add {Γ₁ Γ₂ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h₁ : F₀.IsSymmTwoCocycle Γ₁) (h₂ : F₀.IsSymmTwoCocycle Γ₂) :
    F₀.IsSymmTwoCocycle (Γ₁ + Γ₂) := by
  have hA : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [map_add, h₁.constantCoeff_eq_zero, h₂.constantCoeff_eq_zero, add_zero], ?_, ?_⟩
  · rw [MvPowerSeries.subst_add (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h₁.symm, h₂.symm]
  · rw [MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hFAB hC),
      MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hA hB),
      MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hA hFBC),
      MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hB hC)]
    have e₁ := h₁.cocycle
    have e₂ := h₂.cocycle
    linear_combination e₁ + e₂

theorem isSymmTwoCocycle_smul (a : k) {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h : F₀.IsSymmTwoCocycle Γ) : F₀.IsSymmTwoCocycle (a • Γ) := by
  have hA : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [MvPowerSeries.constantCoeff_smul, h.constantCoeff_eq_zero, smul_zero], ?_, ?_⟩
  · rw [MvPowerSeries.subst_smul (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h.symm]
  · rw [MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hFAB hC),
      MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hA hB),
      MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hA hFBC),
      MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hB hC),
      ← smul_add, ← smul_add, h.cocycle]

variable (F₀)

theorem hasSubst_Xl : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_Xr : HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem addCoboundary_add (g₁ g₂ : MvPowerSeries (Fin n) k) :
    F₀.addCoboundary (g₁ + g₂) = F₀.addCoboundary g₁ + F₀.addCoboundary g₂ := by
  unfold MvFormalGroup.addCoboundary
  rw [MvPowerSeries.subst_add F₀.hasSubst_toPowerSeries, MvPowerSeries.subst_add (hasSubst_Xl (k := k)),
    MvPowerSeries.subst_add (hasSubst_Xr (k := k))]
  ring

theorem addCoboundary_smul (a : k) (g : MvPowerSeries (Fin n) k) :
    F₀.addCoboundary (a • g) = a • F₀.addCoboundary g := by
  unfold MvFormalGroup.addCoboundary
  rw [MvPowerSeries.subst_smul F₀.hasSubst_toPowerSeries, MvPowerSeries.subst_smul (hasSubst_Xl (k := k)),
    MvPowerSeries.subst_smul (hasSubst_Xr (k := k)), smul_sub, smul_sub]

theorem addCoboundary_zero : F₀.addCoboundary 0 = 0 := by
  have h := addCoboundary_smul F₀ (0 : k) 0
  rwa [zero_smul, zero_smul] at h

theorem addCoboundary_neg (g : MvPowerSeries (Fin n) k) :
    F₀.addCoboundary (- g) = - F₀.addCoboundary g := by
  have h := addCoboundary_smul F₀ (-1 : k) g
  rwa [neg_one_smul, neg_one_smul] at h

def Zc : Submodule k (MvPowerSeries (Fin n ⊕ Fin n) k) where
  carrier := {Γ | F₀.IsSymmTwoCocycle Γ}
  add_mem' h₁ h₂ := isSymmTwoCocycle_add h₁ h₂
  zero_mem' := MvFormalGroup.IsSymmTwoCocycle.zero F₀
  smul_mem' a _ h := isSymmTwoCocycle_smul a h

theorem mem_Zc {Γ : MvPowerSeries (Fin n ⊕ Fin n) k} : Γ ∈ Zc F₀ ↔ F₀.IsSymmTwoCocycle Γ := Iff.rfl

def Bc : Submodule k (MvPowerSeries (Fin n ⊕ Fin n) k) where
  carrier := {Γ | ∃ g : MvPowerSeries (Fin n) k, g.constantCoeff = 0 ∧ Γ = F₀.addCoboundary g}
  add_mem' := by
    rintro _ _ ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩
    exact ⟨g₁ + g₂, by rw [map_add, hg₁, hg₂, add_zero], (addCoboundary_add F₀ g₁ g₂).symm⟩
  zero_mem' := ⟨0, map_zero _, (addCoboundary_zero F₀).symm⟩
  smul_mem' := by
    rintro a _ ⟨g, hg, rfl⟩
    exact ⟨a • g, by rw [MvPowerSeries.constantCoeff_smul, hg, smul_zero], (addCoboundary_smul F₀ a g).symm⟩

theorem mem_Bc {Γ : MvPowerSeries (Fin n ⊕ Fin n) k} :
    Γ ∈ Bc F₀ ↔ ∃ g : MvPowerSeries (Fin n) k, g.constantCoeff = 0 ∧ Γ = F₀.addCoboundary g := Iff.rfl

abbrev BinZ : Submodule k (Zc F₀) := (Bc F₀).comap (Zc F₀).subtype

abbrev Qc : Type u := Zc F₀ ⧸ BinZ F₀

theorem mkQ_eq_of_eq_add {Γ Γ' : MvPowerSeries (Fin n ⊕ Fin n) k} (hΓ : Γ ∈ Zc F₀) (hΓ' : Γ' ∈ Zc F₀)
    {g : MvPowerSeries (Fin n) k} (hg : g.constantCoeff = 0) (h : Γ' = Γ + F₀.addCoboundary g) :
    (BinZ F₀).mkQ ⟨Γ, hΓ⟩ = (BinZ F₀).mkQ ⟨Γ', hΓ'⟩ := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨- g, by rw [map_neg, hg, neg_zero], ?_⟩
  show Γ - Γ' = F₀.addCoboundary (-g)
  rw [addCoboundary_neg, h]
  ring

theorem exists_eq_add_of_mkQ_eq {Γ Γ' : MvPowerSeries (Fin n ⊕ Fin n) k} (hΓ : Γ ∈ Zc F₀) (hΓ' : Γ' ∈ Zc F₀)
    (h : (BinZ F₀).mkQ ⟨Γ, hΓ⟩ = (BinZ F₀).mkQ ⟨Γ', hΓ'⟩) :
    ∃ g : MvPowerSeries (Fin n) k, g.constantCoeff = 0 ∧ Γ' = Γ + F₀.addCoboundary g := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨g, hg, hd⟩ := h
  refine ⟨- g, by rw [map_neg, hg, neg_zero], ?_⟩
  change Γ - Γ' = F₀.addCoboundary g at hd
  rw [addCoboundary_neg, ← hd]
  ring

variable {F₀}

end cocycles

end dual

section nose

variable {k : Type u} [Field k] [CharP k q] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

local notation "𝔻" => DualNumber k

def T (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝔻 :=
  MvPowerSeries.subst
    (Sum.elim
      (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
      fun j => (DualNumber.eps : DualNumber k) •
        MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
    (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))

theorem dict : type_of% (MvFormalGroup.translate_injective_and_exists_hom_iff_exists_addCoboundary
    X₀.F (T X₀) (fun _ _ => rfl)) :=
  MvFormalGroup.translate_injective_and_exists_hom_iff_exists_addCoboundary X₀.F (T X₀) (fun _ _ => rfl)

theorem hh₀ : Module.finrank k (MvPowerSeries (Fin 2) k ⧸
    Ideal.span (Set.range (X₀.F.nthSeries q))) = q ^ 4 := by
  obtain ⟨-, -, hrank⟩ := X₀.hasHeight
  have h0 := hrank k (RingHom.id k)
  rw [Series.map_ringHom_id] at h0
  rw [← FormalODModule.act_natCast]
  exact h0

def IsNose (N : FormalODModule q 𝔻) : Prop := N.map (resD k) = X₀.toFormalODModule

variable {X₀}

theorem IsNose.map_F {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) : N.F.map (resD k) = X₀.F :=
  congrArg FormalODModule.F hN

theorem IsNose.map_act {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) (a : Zp2 q) :
    (N.act a).map (resD k) = X₀.act a := by
  have h := congrArg (fun Z : FormalODModule q k => Z.act a) hN
  exact h

theorem IsNose.map_varpi {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) :
    N.varpi.map (resD k) = X₀.varpi := by
  have h := congrArg (fun Z : FormalODModule q k => Z.varpi) hN
  exact h

theorem exists_cocycle {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) :
    ∃ Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k, (∀ l, X₀.F.IsSymmTwoCocycle (Γ l)) ∧
      ∀ i, N.F.toPowerSeries i = T X₀ Γ i :=
  (MvFormalGroup.exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
    X₀.F).2 N.F hN.map_F

def coc {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  (exists_cocycle hN).choose

theorem coc_isCocycle {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) (l : Fin 2) :
    X₀.F.IsSymmTwoCocycle (coc hN l) := (exists_cocycle hN).choose_spec.1 l

theorem coc_cc {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) (l : Fin 2) :
    constantCoeff (coc hN l) = 0 := (coc_isCocycle hN l).constantCoeff_eq_zero

theorem toPowerSeries_eq_T {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) (i : Fin 2) :
    N.F.toPowerSeries i = T X₀ (coc hN) i := (exists_cocycle hN).choose_spec.2 i

theorem coc_unique {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) {Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k}
    (hΓ : ∀ l, constantCoeff (Γ l) = 0) (h : ∀ i, N.F.toPowerSeries i = T X₀ Γ i) : Γ = coc hN :=
  (dict X₀).1 Γ (coc hN) hΓ (coc_cc hN) fun i => (h i).symm.trans (toPowerSeries_eq_T hN i)

structure LineDatum (X₀ : SpecialFormalODModule q j₀) where
  Γb : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k
  hΓb : ∀ l, X₀.F.IsSymmTwoCocycle (Γb l)
  hline : ∀ (N : FormalODModule q 𝔻), IsNose X₀ N →
    ∀ (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k), (∀ l, X₀.F.IsSymmTwoCocycle (Γ l)) →
      (∀ i, N.F.toPowerSeries i = T X₀ Γ i) →
      ∃ (c : k) (g : Fin 2 → MvPowerSeries (Fin 2) k), (∀ l, constantCoeff (g l) = 0) ∧
        ∀ l, Γ l = c • Γb l + X₀.F.addCoboundary (g l)

def LineDatum.Degenerate (Ld : LineDatum X₀) : Prop :=
  ∀ l, ∃ b : MvPowerSeries (Fin 2) k, constantCoeff b = 0 ∧ Ld.Γb l = X₀.F.addCoboundary b

theorem exists_scalar (Ld : LineDatum X₀) {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) :
    ∃ (c : k) (g : Fin 2 → MvPowerSeries (Fin 2) k), (∀ l, constantCoeff (g l) = 0) ∧
      ∀ l, coc hN l = c • Ld.Γb l + X₀.F.addCoboundary (g l) :=
  Ld.hline N hN (coc hN) (coc_isCocycle hN) (toPowerSeries_eq_T hN)

open Classical in

def einv (Ld : LineDatum X₀) {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) : k :=
  if Ld.Degenerate then 0 else (exists_scalar Ld hN).choose

theorem einv_spec (Ld : LineDatum X₀) {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, constantCoeff (g l) = 0) ∧
      ∀ l, coc hN l = einv Ld hN • Ld.Γb l + X₀.F.addCoboundary (g l) := by
  classical
  by_cases hdeg : Ld.Degenerate
  ·
    obtain ⟨c, g, hg, hrel⟩ := exists_scalar Ld hN
    choose b hb0 hb using hdeg
    refine ⟨fun l => c • b l + g l, fun l => ?_, fun l => ?_⟩
    · rw [map_add, MvPowerSeries.constantCoeff_smul, hb0, hg, smul_zero, add_zero]
    · have h0 : einv Ld hN = 0 := by
        unfold einv; rw [if_pos (show Ld.Degenerate from fun l => ⟨b l, hb0 l, hb l⟩)]
      rw [h0, zero_smul, zero_add, addCoboundary_add, addCoboundary_smul, ← hb l]
      exact hrel l
  · have h1 : einv Ld hN = (exists_scalar Ld hN).choose := by unfold einv; rw [if_neg hdeg]
    rw [h1]
    exact (exists_scalar Ld hN).choose_spec

theorem einv_unique (Ld : LineDatum X₀) (hnd : ¬ Ld.Degenerate) {N : FormalODModule q 𝔻} (hN : IsNose X₀ N)
    (c' : k) (g' : Fin 2 → MvPowerSeries (Fin 2) k) (hg' : ∀ l, constantCoeff (g' l) = 0)
    (h : ∀ l, coc hN l = c' • Ld.Γb l + X₀.F.addCoboundary (g' l)) : einv Ld hN = c' := by
  obtain ⟨g, hg, hrel⟩ := einv_spec Ld hN
  by_contra hne
  have hd : einv Ld hN - c' ≠ 0 := sub_ne_zero.mpr hne
  apply hnd
  intro l

  have e1 : (einv Ld hN - c') • Ld.Γb l = X₀.F.addCoboundary (g' l - g l) := by
    have := (hrel l).symm.trans (h l)
    have hsub : X₀.F.addCoboundary (g' l - g l) =
        X₀.F.addCoboundary (g' l) - X₀.F.addCoboundary (g l) := by
      rw [sub_eq_add_neg, addCoboundary_add, addCoboundary_neg, ← sub_eq_add_neg]
    rw [hsub, sub_smul]
    linear_combination this
  refine ⟨(einv Ld hN - c')⁻¹ • (g' l - g l), ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_smul, map_sub, hg', hg, sub_zero, smul_zero]
  · rw [addCoboundary_smul, ← e1, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem lawHom_eq {N₁ N₂ : FormalODModule q 𝔻} (h₁ : IsNose X₀ N₁) (h₂ : IsNose X₀ N₂)
    (α β : N₁.F.Hom N₂.F)
    (h : ∀ i, MvPowerSeries.map (resD k) (α.toPowerSeries i) = MvPowerSeries.map (resD k) (β.toPowerSeries i)) :
    α = β := by
  have hh : Module.finrank k (MvPowerSeries (Fin 2) k ⧸
      Ideal.span (Set.range ((N₁.F.map (resD k)).nthSeries q))) = q ^ 4 := by
    rw [h₁.map_F]
    exact hh₀ X₀
  exact MvFormalGroup.Hom.eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow (resD k) (resD_surjective k) 1
    (ker_resD_sq k) q N₁.F N₂.F 4 hh α β h

theorem isODHom_of_lawHom {N₁ N₂ : FormalODModule q 𝔻} (h₁ : IsNose X₀ N₁) (h₂ : IsNose X₀ N₂)
    (θ : N₁.F.Hom N₂.F) (hθ : ∀ i, MvPowerSeries.map (resD k) (θ.toPowerSeries i) = MvPowerSeries.X i) :
    IsODHom N₁ N₂ θ.toPowerSeries := by
  have hθs : Series.map (resD k) θ.toPowerSeries = Series.id k := funext hθ

  have key : ∀ (e₁ e₂ : Series 𝔻) (he₁ : IsLawHom N₁.F N₁.F e₁) (he₂ : IsLawHom N₂.F N₂.F e₂),
      e₁.map (resD k) = e₂.map (resD k) → Series.comp θ.toPowerSeries e₁ = e₂.comp θ.toPowerSeries := by
    intro e₁ e₂ he₁ he₂ hred
    let α : N₁.F.Hom N₂.F := θ.comp he₁.toHom
    let β : N₁.F.Hom N₂.F := he₂.toHom.comp θ
    have hα : α.toPowerSeries = Series.comp θ.toPowerSeries e₁ := rfl
    have hβ : β.toPowerSeries = e₂.comp θ.toPowerSeries := rfl
    have hαβ : α = β := by
      refine lawHom_eq h₁ h₂ α β fun i => ?_
      have hαr : Series.map (resD k) α.toPowerSeries = (Series.id k).comp (e₁.map (resD k)) := by
        rw [hα, Series.map_comp _ _ _ he₁.1, hθs]
      have hβr : Series.map (resD k) β.toPowerSeries = (e₂.map (resD k)).comp (Series.id k) := by
        rw [hβ, Series.map_comp _ _ _ θ.constantCoeff_eq_zero, hθs]
      have h' : Series.map (resD k) α.toPowerSeries = Series.map (resD k) β.toPowerSeries := by
        rw [hαr, hβr, Series.comp_id, Series.id_comp _ (cc_map he₁.1 _), hred]
      exact congrFun h' i
    rw [← hα, ← hβ, hαβ]
  refine ⟨IsLawHom.of_hom θ, fun a => ?_, ?_⟩
  · exact key (N₁.act a) (N₂.act a) (N₁.isLawHom_act a) (N₂.isLawHom_act a)
      (by rw [h₁.map_act, h₂.map_act])
  · exact key N₁.varpi N₂.varpi N₁.isLawHom_varpi N₂.isLawHom_varpi
      (by rw [h₁.map_varpi, h₂.map_varpi])

theorem exists_iso_of_coc_eq_add {N₁ N₂ : FormalODModule q 𝔻} (h₁ : IsNose X₀ N₁) (h₂ : IsNose X₀ N₂)
    (g : Fin 2 → MvPowerSeries (Fin 2) k) (hg : ∀ l, constantCoeff (g l) = 0)
    (hrel : ∀ l, coc h₂ l = coc h₁ l + X₀.F.addCoboundary (g l)) :
    ∃ v : N₁.Hom N₂, v.IsIso ∧ v.toSeries.map (resD k) = Series.id k := by
  have D2 := (dict X₀).2.1

  obtain ⟨θ, hθ⟩ := (D2 (coc h₁) (coc h₂) (coc_cc h₁) (coc_cc h₂) N₁.F N₂.F
    (toPowerSeries_eq_T h₁) (toPowerSeries_eq_T h₂)).mpr ⟨g, hg, hrel⟩
  have hng : ∀ l, constantCoeff (- g l) = 0 := fun l => by rw [map_neg, hg l, neg_zero]
  have hrel' : ∀ l, coc h₁ l = coc h₂ l + X₀.F.addCoboundary (- g l) := fun l => by
    rw [hrel l, addCoboundary_neg]; ring
  obtain ⟨θ', hθ'⟩ := (D2 (coc h₂) (coc h₁) (coc_cc h₂) (coc_cc h₁) N₂.F N₁.F
    (toPowerSeries_eq_T h₂) (toPowerSeries_eq_T h₁)).mpr ⟨fun l => - g l, hng, hrel'⟩
  have hθs : Series.map (resD k) θ.toPowerSeries = Series.id k := funext hθ
  have hθ's : Series.map (resD k) θ'.toPowerSeries = Series.id k := funext hθ'

  have h11 : θ'.comp θ = MvFormalGroup.Hom.id N₁.F := by
    refine lawHom_eq h₁ h₁ _ _ fun i => ?_
    have e : Series.map (resD k) (θ'.comp θ).toPowerSeries = Series.id k := by
      show Series.map (resD k) (Series.comp θ'.toPowerSeries θ.toPowerSeries) = Series.id k
      rw [Series.map_comp _ _ _ θ.constantCoeff_eq_zero, hθs, hθ's, Series.comp_id]
    have e' : Series.map (resD k) (MvFormalGroup.Hom.id N₁.F).toPowerSeries = Series.id k :=
      Series.map_id _
    exact (congrFun e i).trans (congrFun e' i).symm
  have h22 : θ.comp θ' = MvFormalGroup.Hom.id N₂.F := by
    refine lawHom_eq h₂ h₂ _ _ fun i => ?_
    have e : Series.map (resD k) (θ.comp θ').toPowerSeries = Series.id k := by
      show Series.map (resD k) (Series.comp θ.toPowerSeries θ'.toPowerSeries) = Series.id k
      rw [Series.map_comp _ _ _ θ'.constantCoeff_eq_zero, hθs, hθ's, Series.comp_id]
    have e' : Series.map (resD k) (MvFormalGroup.Hom.id N₂.F).toPowerSeries = Series.id k :=
      Series.map_id _
    exact (congrFun e i).trans (congrFun e' i).symm
  let v : N₁.Hom N₂ := ⟨θ.toPowerSeries, isODHom_of_lawHom h₁ h₂ θ hθ⟩
  let v' : N₂.Hom N₁ := ⟨θ'.toPowerSeries, isODHom_of_lawHom h₂ h₁ θ' hθ'⟩
  refine ⟨v, ⟨v', FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩, hθs⟩
  · exact congrArg MvFormalGroup.Hom.toPowerSeries h11
  · exact congrArg MvFormalGroup.Hom.toPowerSeries h22

theorem exists_coc_eq_add_of_hom {N₁ N₂ : FormalODModule q 𝔻} (h₁ : IsNose X₀ N₁) (h₂ : IsNose X₀ N₂)
    (v : N₁.Hom N₂) (hv : v.toSeries.map (resD k) = Series.id k) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, constantCoeff (g l) = 0) ∧
      ∀ l, coc h₂ l = coc h₁ l + X₀.F.addCoboundary (g l) :=
  ((dict X₀).2.1 (coc h₁) (coc h₂) (coc_cc h₁) (coc_cc h₂) N₁.F N₂.F
    (toPowerSeries_eq_T h₁) (toPowerSeries_eq_T h₂)).mp ⟨v.toLawHom, congrFun hv⟩

theorem einv_eq_of_hom (Ld : LineDatum X₀) {N₁ N₂ : FormalODModule q 𝔻} (h₁ : IsNose X₀ N₁) (h₂ : IsNose X₀ N₂)
    (v : N₁.Hom N₂) (hv : v.toSeries.map (resD k) = Series.id k) : einv Ld h₁ = einv Ld h₂ := by
  classical
  by_cases hdeg : Ld.Degenerate
  · unfold einv; rw [if_pos hdeg, if_pos hdeg]
  obtain ⟨g, hg, hrel⟩ := exists_coc_eq_add_of_hom h₁ h₂ v hv
  obtain ⟨g₁, hg₁, hrel₁⟩ := einv_spec Ld h₁
  symm
  refine einv_unique Ld hdeg h₂ (einv Ld h₁) (fun l => g₁ l + g l)
    (fun l => by rw [map_add, hg₁, hg, add_zero]) fun l => ?_
  rw [hrel l, hrel₁ l, addCoboundary_add]
  ring

theorem exists_iso_of_einv_eq (Ld : LineDatum X₀) {N₁ N₂ : FormalODModule q 𝔻} (h₁ : IsNose X₀ N₁)
    (h₂ : IsNose X₀ N₂) (h : einv Ld h₁ = einv Ld h₂) :
    ∃ v : N₁.Hom N₂, v.IsIso ∧ v.toSeries.map (resD k) = Series.id k := by
  obtain ⟨g₁, hg₁, hrel₁⟩ := einv_spec Ld h₁
  obtain ⟨g₂, hg₂, hrel₂⟩ := einv_spec Ld h₂
  refine exists_iso_of_coc_eq_add h₁ h₂ (fun l => g₂ l - g₁ l)
    (fun l => by rw [map_sub, hg₁, hg₂, sub_zero]) fun l => ?_
  show coc h₂ l = coc h₁ l + X₀.F.addCoboundary (g₂ l - g₁ l)
  rw [sub_eq_add_neg, addCoboundary_add, addCoboundary_neg, hrel₂ l, hrel₁ l, ← h]
  ring

theorem isNose_map_mu {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) (μ : 𝔻 →+* 𝔻)
    (hμ : (resD k).comp μ = resD k) : IsNose X₀ (N.map μ) := by
  show (N.map μ).map (resD k) = X₀.toFormalODModule
  rw [FormalODModule.map_map, hμ]
  exact hN

theorem einv_map_mu (Ld : LineDatum X₀) {N : FormalODModule q 𝔻} (hN : IsNose X₀ N) (c : k) (μ : 𝔻 →+* 𝔻)
    (hμ : (resD k).comp μ = resD k) (hμc : ∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) :
    einv Ld (isNose_map_mu hN μ hμ) = c • einv Ld hN := by
  classical
  have hcoc : (fun l => c • coc hN l) = coc (isNose_map_mu hN μ hμ) := by
    refine coc_unique _ (fun l => by rw [MvPowerSeries.constantCoeff_smul, coc_cc, smul_zero]) fun i => ?_
    show MvPowerSeries.map μ (N.F.toPowerSeries i) = T X₀ (fun l => c • coc hN l) i
    rw [toPowerSeries_eq_T hN i]
    exact (dict X₀).2.2.2 c μ hμ hμc (coc hN) (coc_cc hN) i
  by_cases hdeg : Ld.Degenerate
  · unfold einv; rw [if_pos hdeg, if_pos hdeg, smul_zero]
  obtain ⟨g, hg, hrel⟩ := einv_spec Ld hN
  rw [smul_eq_mul]
  refine einv_unique Ld hdeg _ (c * einv Ld hN) (fun l => c • g l)
    (fun l => by rw [MvPowerSeries.constantCoeff_smul, hg, smul_zero]) fun l => ?_
  rw [← congrFun hcoc l]
  show c • coc hN l = (c * einv Ld hN) • Ld.Γb l + X₀.F.addCoboundary (c • g l)
  rw [hrel l, smul_add, smul_smul, addCoboundary_smul]

theorem isNose_map_of {B : Type u} [CommRing B] (resB : B →+* k) {Y : FormalODModule q B}
    (hY : Y.map resB = X₀.toFormalODModule) (p : B →+* 𝔻) (hp : (resD k).comp p = resB) :
    IsNose X₀ (Y.map p) := by
  show (Y.map p).map (resD k) = X₀.toFormalODModule
  rw [FormalODModule.map_map, hp]
  exact hY

theorem map_sigma_eq {B : Type u} [CommRing B] (resB : B →+* k) (p₁ p₂ σ : B →+* 𝔻)
    (hp₁ : (resD k).comp p₁ = resB) (hp₂ : (resD k).comp p₂ = resB) (hσ : (resD k).comp σ = resB)
    (hadd : ∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b))
    {τ : Type*} (f : MvPowerSeries τ B) :
    MvPowerSeries.map σ f + MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (MvPowerSeries.map resB f) =
      MvPowerSeries.map p₁ f + MvPowerSeries.map p₂ f := by
  refine MvPowerSeries.ext fun d => ?_
  simp only [map_add, MvPowerSeries.coeff_map]
  have e₁ := congrArg (fun r : B →+* k => r (coeff d f)) hp₁
  have e₂ := congrArg (fun r : B →+* k => r (coeff d f)) hp₂
  have e₃ := congrArg (fun r : B →+* k => r (coeff d f)) hσ
  simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂ e₃
  change TrivSqZeroExt.fst (p₁ (coeff d f)) = resB (coeff d f) at e₁
  change TrivSqZeroExt.fst (p₂ (coeff d f)) = resB (coeff d f) at e₂
  change TrivSqZeroExt.fst (σ (coeff d f)) = resB (coeff d f) at e₃
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [e₁, e₂, e₃]
  · simp [hadd]

theorem einv_add (Ld : LineDatum X₀) {B : Type u} [CommRing B] (resB : B →+* k) {Y : FormalODModule q B}
    (hY : Y.map resB = X₀.toFormalODModule) (p₁ p₂ σ : B →+* 𝔻)
    (hp₁ : (resD k).comp p₁ = resB) (hp₂ : (resD k).comp p₂ = resB) (hσ : (resD k).comp σ = resB)
    (hadd : ∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) :
    einv Ld (isNose_map_of resB hY σ hσ) =
      einv Ld (isNose_map_of resB hY p₁ hp₁) + einv Ld (isNose_map_of resB hY p₂ hp₂) := by
  classical
  set h₁ := isNose_map_of (X₀ := X₀) resB hY p₁ hp₁
  set h₂ := isNose_map_of (X₀ := X₀) resB hY p₂ hp₂
  set hs := isNose_map_of (X₀ := X₀) resB hY σ hσ
  have hYF : Y.F.map resB = X₀.F := congrArg FormalODModule.F hY
  have hcoc : (fun l => coc h₁ l + coc h₂ l) = coc hs := by
    refine coc_unique _ (fun l => by rw [map_add, coc_cc, coc_cc, add_zero]) fun i => ?_
    have h3 := (dict X₀).2.2.1 (coc h₁) (coc h₂) (coc_cc h₁) (coc_cc h₂) i
    have e1 : T X₀ (coc h₁) i = MvPowerSeries.map p₁ (Y.F.toPowerSeries i) := (toPowerSeries_eq_T h₁ i).symm
    have e2 : T X₀ (coc h₂) i = MvPowerSeries.map p₂ (Y.F.toPowerSeries i) := (toPowerSeries_eq_T h₂ i).symm
    have es : (Y.map σ).F.toPowerSeries i = MvPowerSeries.map σ (Y.F.toPowerSeries i) := rfl
    have hm := map_sigma_eq resB p₁ p₂ σ hp₁ hp₂ hσ hadd (Y.F.toPowerSeries i)
    have hX0 : MvPowerSeries.map resB (Y.F.toPowerSeries i) = X₀.F.toPowerSeries i := by
      rw [← hYF]; rfl
    rw [hX0] at hm
    rw [es]
    rw [e1, e2] at h3
    exact add_right_cancel (hm.trans h3.symm)
  by_cases hdeg : Ld.Degenerate
  · unfold einv; rw [if_pos hdeg, if_pos hdeg, if_pos hdeg, add_zero]
  obtain ⟨g₁, hg₁, hrel₁⟩ := einv_spec Ld h₁
  obtain ⟨g₂, hg₂, hrel₂⟩ := einv_spec Ld h₂
  refine einv_unique Ld hdeg _ (einv Ld h₁ + einv Ld h₂) (fun l => g₁ l + g₂ l)
    (fun l => by rw [map_add, hg₁, hg₂, add_zero]) fun l => ?_
  rw [← congrFun hcoc l]
  show coc h₁ l + coc h₂ l = (einv Ld h₁ + einv Ld h₂) • Ld.Γb l + X₀.F.addCoboundary (g₁ l + g₂ l)
  rw [hrel₁ l, hrel₂ l, add_smul, addCoboundary_add]
  ring

theorem exists_nose_over {B : Type u} [CommRing B] (resB : B →+* k) (hs : Function.Surjective resB)
    (hloc : IsLocalHom resB) (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule)
    (hu : u.IsIso) :
    ∃ Y' : FormalODModule q B, Y'.map resB = X₀.toFormalODModule ∧
      ∃ v : Y'.Hom Y, v.IsIso ∧ u.toSeries.comp (v.toSeries.map resB) = Series.id k := by
  obtain ⟨part1, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective X₀
      (B := B) (A' := k) (A'' := B) (A := k)
      resB (RingHom.id B) (RingHom.id k) resB (RingHom.ext fun _ => rfl)
      (fun a' a'' h => ⟨a'', ⟨h.symm, rfl⟩, fun b hb => hb.2⟩) hs hloc
      resB (RingHom.id k) resB (RingHom.id k)
      (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl)
      (RingHom.ext fun _ => rfl) Function.surjective_id
      ⟨1, by rw [pow_one, (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id]; rfl⟩
  obtain ⟨g, hg₁, hg₂⟩ := exists_inv hu
  have hgiso : g.IsIso := ⟨u, FormalODModule.Hom.ext hg₂, FormalODModule.Hom.ext hg₁⟩
  have hmid : X₀.toFormalODModule.map (RingHom.id k) = X₀.toFormalODModule := FormalODModule.map_id _
  let w' : (X₀.toFormalODModule.map (RingHom.id k)).Hom X₀.toFormalODModule :=
    castHom hmid.symm (FormalODModule.Hom.id _)
  have hw' : w'.IsIso := castHom_isIso _ _ (id_isIso _)
  let φ' : (X₀.toFormalODModule.map (RingHom.id k)).Hom (Y.map resB) := castHom hmid.symm g
  have hφ' : φ'.IsIso := castHom_isIso _ _ hgiso
  have hcompat : u.toSeries.comp (φ'.toSeries.map (RingHom.id k)) = w'.toSeries := by
    show u.toSeries.comp (g.toSeries.map (RingHom.id k)) = Series.id k
    rw [Series.map_ringHom_id, hg₂]
  obtain ⟨Y', u', -, hY', hu', v, hv, -, hc⟩ := part1 X₀.toFormalODModule w' hw' Y u hu φ' hφ' hcompat
  have hvid : Y'.map (RingHom.id B) = Y' := FormalODModule.map_id _
  refine ⟨Y', hY', castHom hvid v, castHom_isIso _ _ hv, ?_⟩
  show u.toSeries.comp (v.toSeries.map resB) = Series.id k
  rw [hc, hu']
  rfl

structure Norm (X : FormalODModule q 𝔻) (w : (X.map (resD k)).Hom X₀.toFormalODModule) where
  N : FormalODModule q 𝔻
  hN : IsNose X₀ N
  v : N.Hom X
  hv : v.IsIso
  hc : w.toSeries.comp (v.toSeries.map (resD k)) = Series.id k

theorem nonempty_norm (X : FormalODModule q 𝔻) (w : (X.map (resD k)).Hom X₀.toFormalODModule)
    (hw : w.IsIso) : Nonempty (Norm (X₀ := X₀) X w) := by
  obtain ⟨N, hN, v, hv, hc⟩ := exists_nose_over (X₀ := X₀) (resD k) (resD_surjective k)
    (isLocalHom_resD k) X w hw
  exact ⟨⟨N, hN, v, hv, hc⟩⟩

def norm (X : FormalODModule q 𝔻) (w : (X.map (resD k)).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    Norm (X₀ := X₀) X w :=
  (nonempty_norm X w hw).some

theorem einv_norm_eq (Ld : LineDatum X₀) {X : FormalODModule q 𝔻} {w : (X.map (resD k)).Hom X₀.toFormalODModule}
    (nX : Norm (X₀ := X₀) X w)
    {X' : FormalODModule q 𝔻} {w' : (X'.map (resD k)).Hom X₀.toFormalODModule} (hw' : w'.IsIso)
    (nX' : Norm (X₀ := X₀) X' w')
    (v₀ : X.Hom X') (hc₀ : w'.toSeries.comp (v₀.toSeries.map (resD k)) = w.toSeries) :
    einv Ld nX.hN = einv Ld nX'.hN := by
  obtain ⟨g', hg'₁, hg'₂⟩ := exists_inv nX'.hv

  refine einv_eq_of_hom Ld nX.hN nX'.hN (g'.comp (v₀.comp nX.v)) ?_

  obtain ⟨gw, hgw₁, hgw₂⟩ := exists_inv hw'
  have hv'k₁ : (g'.toSeries.map (resD k)).comp (nX'.v.toSeries.map (resD k)) = Series.id k := by
    rw [← Series.map_comp _ _ _ (hom_cc nX'.v), hg'₁, Series.map_id]
  have hv'k₂ : (nX'.v.toSeries.map (resD k)).comp (g'.toSeries.map (resD k)) = Series.id k := by
    rw [← Series.map_comp _ _ _ (hom_cc g'), hg'₂, Series.map_id]
  have hw'eq : w'.toSeries = g'.toSeries.map (resD k) :=
    inverse_unique (cc_map (hom_cc nX'.v) _) (cc_map (hom_cc g') _) nX'.hc hv'k₂
  show ((g'.toSeries.comp (v₀.toSeries.comp nX.v.toSeries)).map (resD k)) = Series.id k
  rw [Series.map_comp _ _ _ (Series.constantCoeff_comp (hom_cc v₀) (hom_cc nX.v)),
    Series.map_comp _ _ _ (hom_cc nX.v), ← hw'eq,
    ← Series.comp_assoc _ _ _ (cc_map (hom_cc v₀) _) (cc_map (hom_cc nX.v) _), hc₀, nX.hc]

def e (Ld : LineDatum X₀) (X : FormalODModule q 𝔻) (w : (X.map (resD k)).Hom X₀.toFormalODModule)
    (hw : w.IsIso) : k :=
  einv Ld (norm X w hw).hN

theorem e_eq_of_iso (Ld : LineDatum X₀) (X : FormalODModule q 𝔻) (w : (X.map (resD k)).Hom X₀.toFormalODModule)
    (hw : w.IsIso)
    (X' : FormalODModule q 𝔻) (w' : (X'.map (resD k)).Hom X₀.toFormalODModule) (hw' : w'.IsIso)
    (v : X.Hom X') (hc : w'.toSeries.comp (v.toSeries.map (resD k)) = w.toSeries) :
    e Ld X w hw = e Ld X' w' hw' :=
  einv_norm_eq Ld (norm X w hw) hw' (norm X' w' hw') v hc

theorem exists_iso_of_e_eq (Ld : LineDatum X₀) (X : FormalODModule q 𝔻)
    (w : (X.map (resD k)).Hom X₀.toFormalODModule)
    (hw : w.IsIso) (X' : FormalODModule q 𝔻) (w' : (X'.map (resD k)).Hom X₀.toFormalODModule)
    (hw' : w'.IsIso) (h : e Ld X w hw = e Ld X' w' hw') :
    ∃ v : X.Hom X', v.IsIso ∧ w'.toSeries.comp (v.toSeries.map (resD k)) = w.toSeries := by
  set n₁ := norm (X₀ := X₀) X w hw
  set n₂ := norm (X₀ := X₀) X' w' hw'
  obtain ⟨θ, hθ, hθk⟩ := exists_iso_of_einv_eq Ld n₁.hN n₂.hN h
  obtain ⟨g₁, hg₁₁, hg₁₂⟩ := exists_inv n₁.hv
  have hg₁iso : g₁.IsIso := ⟨n₁.v, FormalODModule.Hom.ext hg₁₂, FormalODModule.Hom.ext hg₁₁⟩
  refine ⟨n₂.v.comp (θ.comp g₁), isIso_comp n₂.hv (isIso_comp hθ hg₁iso), ?_⟩

  have hg₁k₁ : (g₁.toSeries.map (resD k)).comp (n₁.v.toSeries.map (resD k)) = Series.id k := by
    rw [← Series.map_comp _ _ _ (hom_cc n₁.v), hg₁₁, Series.map_id]
  have hg₁k₂ : (n₁.v.toSeries.map (resD k)).comp (g₁.toSeries.map (resD k)) = Series.id k := by
    rw [← Series.map_comp _ _ _ (hom_cc g₁), hg₁₂, Series.map_id]
  have hweq : w.toSeries = g₁.toSeries.map (resD k) :=
    inverse_unique (cc_map (hom_cc n₁.v) _) (cc_map (hom_cc g₁) _) n₁.hc hg₁k₂
  show w'.toSeries.comp ((n₂.v.toSeries.comp (θ.toSeries.comp g₁.toSeries)).map (resD k)) = w.toSeries
  rw [Series.map_comp _ _ _ (Series.constantCoeff_comp (hom_cc θ) (hom_cc g₁)),
    Series.map_comp _ _ _ (hom_cc g₁), hθk,
    ← Series.comp_assoc _ _ _ (cc_map (hom_cc n₂.v) _)
      (Series.constantCoeff_comp (cc_id) (cc_map (hom_cc g₁) _)),
    n₂.hc, Series.id_comp _ (Series.constantCoeff_comp (cc_id) (cc_map (hom_cc g₁) _)),
    Series.id_comp _ (cc_map (hom_cc g₁) _), hweq]

theorem e_map_mu (Ld : LineDatum X₀) (c : k) (μ : 𝔻 →+* 𝔻) (hμ : (resD k).comp μ = resD k)
    (hμc : ∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t)
    (X : FormalODModule q 𝔻) (w : (X.map (resD k)).Hom X₀.toFormalODModule) (hw : w.IsIso)
    (w' : ((X.map μ).map (resD k)).Hom X₀.toFormalODModule) (hw' : w'.IsIso)
    (hww : w'.toSeries = w.toSeries) :
    e Ld (X.map μ) w' hw' = c • e Ld X w hw := by
  set n₁ := norm (X₀ := X₀) X w hw

  let nμ : Norm (X₀ := X₀) (X.map μ) w' :=
    { N := n₁.N.map μ
      hN := isNose_map_mu n₁.hN μ hμ
      v := n₁.v.map μ
      hv := isIso_map μ n₁.hv
      hc := by
        show w'.toSeries.comp ((n₁.v.toSeries.map μ).map (resD k)) = Series.id k
        rw [Series.map_map, hμ, hww]
        exact n₁.hc }
  have h1 : e Ld (X.map μ) w' hw' = einv Ld nμ.hN := by
    refine einv_norm_eq Ld (norm (X.map μ) w' hw') hw' nμ (FormalODModule.Hom.id _) ?_
    rw [id_toSeries, Series.map_id, Series.comp_id]
  rw [h1]
  exact einv_map_mu Ld n₁.hN c μ hμ hμc

theorem e_add (Ld : LineDatum X₀) {B : Type u} [CommRing B] (resB : B →+* k) (hsB : Function.Surjective resB)
    (hloc : IsLocalHom resB) (p₁ p₂ σ : B →+* 𝔻)
    (hp₁ : (resD k).comp p₁ = resB) (hp₂ : (resD k).comp p₂ = resB) (hσ : (resD k).comp σ = resB)
    (hadd : ∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b))
    (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule) (hu : u.IsIso)
    (w₁ : ((Y.map p₁).map (resD k)).Hom X₀.toFormalODModule) (hw₁ : w₁.IsIso)
    (w₂ : ((Y.map p₂).map (resD k)).Hom X₀.toFormalODModule) (hw₂ : w₂.IsIso)
    (wσ : ((Y.map σ).map (resD k)).Hom X₀.toFormalODModule) (hwσ : wσ.IsIso)
    (h₁ : w₁.toSeries = u.toSeries) (h₂ : w₂.toSeries = u.toSeries) (hs : wσ.toSeries = u.toSeries) :
    e Ld (Y.map σ) wσ hwσ = e Ld (Y.map p₁) w₁ hw₁ + e Ld (Y.map p₂) w₂ hw₂ := by

  obtain ⟨Y', hY', v, hv, hc⟩ := exists_nose_over (X₀ := X₀) resB hsB hloc Y u hu

  have key : ∀ (p : B →+* 𝔻) (hp : (resD k).comp p = resB)
      (wp : ((Y.map p).map (resD k)).Hom X₀.toFormalODModule) (hwp : wp.IsIso)
      (hwpu : wp.toSeries = u.toSeries),
      e Ld (Y.map p) wp hwp = einv Ld (isNose_map_of resB hY' p hp) := by
    intro p hp wp hwp hwpu
    let np : Norm (X₀ := X₀) (Y.map p) wp :=
      { N := Y'.map p
        hN := isNose_map_of resB hY' p hp
        v := v.map p
        hv := isIso_map p hv
        hc := by
          show wp.toSeries.comp ((v.toSeries.map p).map (resD k)) = Series.id k
          rw [Series.map_map, hp, hwpu]
          exact hc }
    refine einv_norm_eq Ld (norm (Y.map p) wp hwp) hwp np (FormalODModule.Hom.id _) ?_
    rw [id_toSeries, Series.map_id, Series.comp_id]
  rw [key p₁ hp₁ w₁ hw₁ h₁, key p₂ hp₂ w₂ hw₂ h₂, key σ hσ wσ hwσ hs]
  exact einv_add Ld resB hY' p₁ p₂ σ hp₁ hp₂ hσ hadd

end nose

end F2aLine
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and.F2aLine"

open F2aLine CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ (e : ∀ (X : FormalODModule q (DualNumber k))
        (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule),
        w.IsIso → (Fin 1 → k)),

      (∀ (X : FormalODModule q (DualNumber k))
          (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber k))
          (w' : (X'.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso) (v : X.Hom X'), v.IsIso →
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = w.toSeries →
        e X w hw = e X' w' hw') ∧

      (∀ (X : FormalODModule q (DualNumber k))
          (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber k))
          (w' : (X'.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso),
        e X w hw = e X' w' hw' →
        ∃ v : X.Hom X', v.IsIso ∧
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = w.toSeries) ∧

      (∀ (c : k) (μ : DualNumber k →+* DualNumber k),
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp μ = (TrivSqZeroExt.fstHom k k k).toRingHom →
          (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ (X : FormalODModule q (DualNumber k))
          (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (w' : ((X.map μ).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso), w'.toSeries = w.toSeries →
        e (X.map μ) w' hw' = c • e X w hw) ∧

      (∀ (B : Type u) [CommRing B] (resB : B →+* k), Function.Surjective resB → IsLocalHom resB →
        ∀ (p₁ p₂ σ : B →+* DualNumber k),
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp p₁ = resB →
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp p₂ = resB →
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp σ = resB →
          (∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule), u.IsIso →
        ∀ (w₁ : ((Y.map p₁).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw₁ : w₁.IsIso)
          (w₂ : ((Y.map p₂).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw₂ : w₂.IsIso)
          (wσ : ((Y.map σ).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hwσ : wσ.IsIso),
          w₁.toSeries = u.toSeries → w₂.toSeries = u.toSeries → wσ.toSeries = u.toSeries →
        e (Y.map σ) wσ hwσ = e (Y.map p₁) w₁ hw₁ + e (Y.map p₂) w₂ hw₂) := by
  classical

  obtain ⟨Γb, hΓb, hline⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
      X₀ hsmooth
  let Ld : F2aLine.LineDatum X₀ := ⟨Γb, hΓb, fun N hN Γ hΓ hT => hline N hN Γ hΓ hT⟩
  refine ⟨fun X w hw _ => F2aLine.e Ld X w hw, ?_, ?_, ?_, ?_⟩
  · intro X w hw X' w' hw' v _ hc
    funext m
    exact e_eq_of_iso Ld X w hw X' w' hw' v hc
  · intro X w hw X' w' hw' h
    exact exists_iso_of_e_eq Ld X w hw X' w' hw' (congrFun h 0)
  · intro c μ hμ hμc X w hw w' hw' hww
    funext m
    show F2aLine.e Ld (X.map μ) w' hw' = c • F2aLine.e Ld X w hw
    exact e_map_mu Ld c μ hμ hμc X w hw w' hw' hww
  · intro B _ resB hsB hloc p₁ p₂ σ hp₁ hp₂ hσ hadd Y u hu w₁ hw₁ w₂ hw₂ wσ hwσ h₁ h₂ hs
    funext m
    exact e_add Ld resB hsB hloc p₁ p₂ σ hp₁ hp₂ hσ hadd Y u hu w₁ hw₁ w₂ hw₂ wσ hwσ h₁ h₂ hs

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and.F2aLine"

end S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and (solution)
