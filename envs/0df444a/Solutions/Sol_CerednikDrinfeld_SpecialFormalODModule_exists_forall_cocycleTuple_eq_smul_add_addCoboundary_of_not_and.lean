-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3077f55d-dd0d-55a4-8215-2014dbf1791b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_act_smul_eq_subst_act_add_addCoboundary
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

noncomputable section

namespace CLineAsm

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

section asm

variable {k : Type u} [Field k] [CharP k q] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

def pullF (φ : Series k) : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  Sum.elim
    (fun i => subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
    fun i => subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i)

omit X₀ in
theorem pullF_cc {φ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) (s : Fin 2 ⊕ Fin 2) :
    constantCoeff (pullF φ s) = 0 := by
  rcases s with i | i
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)
      (fun m => constantCoeff_X _) (hφ i)
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)
      (fun m => constantCoeff_X _) (hφ i)

omit X₀ in
theorem hasSubst_pullF {φ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) : HasSubst (pullF φ) :=
  hasSubst_of_constantCoeff_zero (pullF_cc hφ)

abbrev Q : Type u := MvPowerSeries (Fin 2 ⊕ Fin 2) k ⧸ Bc X₀.F

private abbrev _root_.CLineAsm.mk : MvPowerSeries (Fin 2 ⊕ Fin 2) k →ₗ[k] Q X₀ := (Bc X₀.F).mkQ

p2m_export "CLineAsm" "mk"
theorem mk_addCoboundary {g : MvPowerSeries (Fin 2) k} (hg : constantCoeff g = 0) :
    mk X₀ (X₀.F.addCoboundary g) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨g, hg, rfl⟩

theorem exists_of_mk_eq {Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (h : mk X₀ Γ = mk X₀ Γ') :
    ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧ Γ = Γ' + X₀.F.addCoboundary g := by
  obtain ⟨g, hg, hd⟩ := (Submodule.Quotient.eq _).mp h
  exact ⟨g, hg, by rw [← hd]; abel⟩

def rho (φ : Series k) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hB : ∀ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 →
      constantCoeff (subst φ g) = 0 ∧ subst (pullF φ) (X₀.F.addCoboundary g) = X₀.F.addCoboundary (subst φ g)) :
    Q X₀ →ₗ[k] Q X₀ :=
  (Bc X₀.F).mapQ (Bc X₀.F) (MvPowerSeries.substAlgHom (hasSubst_pullF hφ)).toLinearMap (by
    rintro Γ ⟨g, hg, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨subst φ g, (hB g hg).1, ?_⟩
    show MvPowerSeries.substAlgHom (hasSubst_pullF hφ) (X₀.F.addCoboundary g) = _
    rw [MvPowerSeries.substAlgHom_apply]
    exact (hB g hg).2)

theorem rho_mk (φ : Series k) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hB : ∀ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 →
      constantCoeff (subst φ g) = 0 ∧ subst (pullF φ) (X₀.F.addCoboundary g) = X₀.F.addCoboundary (subst φ g))
    (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) :
    rho X₀ φ hφ hB (mk X₀ Γ) = mk X₀ (subst (pullF φ) Γ) := by
  show (Bc X₀.F).mapQ (Bc X₀.F) _ _ (Submodule.Quotient.mk Γ) = Submodule.Quotient.mk _
  rw [Submodule.mapQ_apply]
  simp only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, MvPowerSeries.substAlgHom_apply]

def mv (M : Matrix (Fin 2) (Fin 2) k) (x : Fin 2 → Q X₀) : Fin 2 → Q X₀ := fun l => ∑ i, M l i • x i

theorem mv_apply (M : Matrix (Fin 2) (Fin 2) k) (x : Fin 2 → Q X₀) (l : Fin 2) :
    mv X₀ M x l = M l 0 • x 0 + M l 1 • x 1 := by
  simp [mv, Fin.sum_univ_two]

theorem mv_mv (M N : Matrix (Fin 2) (Fin 2) k) (x : Fin 2 → Q X₀) :
    mv X₀ M (mv X₀ N x) = mv X₀ (M * N) x := by
  funext l
  simp only [mv_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_add, smul_smul, add_smul]
  abel

theorem mv_one (x : Fin 2 → Q X₀) : mv X₀ 1 x = x := by
  funext l
  fin_cases l <;> simp [mv_apply]

theorem map_mv (f : Q X₀ →ₗ[k] Q X₀) (M : Matrix (Fin 2) (Fin 2) k) (x : Fin 2 → Q X₀) :
    (fun l => f (mv X₀ M x l)) = mv X₀ M (fun l => f (x l)) := by
  funext l
  simp only [mv_apply, map_add, map_smul]

theorem act_cc (a : Zp2 q) : ∀ i, constantCoeff (X₀.act a i) = 0 := (X₀.isLawHom_act a).1
theorem varpi_cc : ∀ i, constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1

theorem hB_act (a : Zp2 q) : ∀ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 →
      constantCoeff (subst (X₀.act a) g) = 0 ∧
        subst (pullF (X₀.act a)) (X₀.F.addCoboundary g) = X₀.F.addCoboundary (subst (X₀.act a) g) :=
  ((CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add X₀).1 (X₀.act a)
    (Or.inr ⟨a, rfl⟩)).2

theorem hB_varpi : ∀ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 →
      constantCoeff (subst X₀.varpi g) = 0 ∧
        subst (pullF X₀.varpi) (X₀.F.addCoboundary g) = X₀.F.addCoboundary (subst X₀.varpi g) :=
  ((CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add X₀).1 X₀.varpi
    (Or.inl rfl)).2

theorem hZ_varpi : ∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, X₀.F.IsSymmTwoCocycle Γ →
    X₀.F.IsSymmTwoCocycle (subst (pullF X₀.varpi) Γ) :=
  ((CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add X₀).1 X₀.varpi
    (Or.inl rfl)).1

def ρa (a : Zp2 q) : Q X₀ →ₗ[k] Q X₀ := rho X₀ (X₀.act a) (act_cc X₀ a) (hB_act X₀ a)

def ρv : Q X₀ →ₗ[k] Q X₀ := rho X₀ X₀.varpi (varpi_cc X₀) (hB_varpi X₀)

theorem ρa_mk (a : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) :
    ρa X₀ a (mk X₀ Γ) = mk X₀ (subst (pullF (X₀.act a)) Γ) := rho_mk X₀ _ _ _ Γ
theorem ρv_mk (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) :
    ρv X₀ (mk X₀ Γ) = mk X₀ (subst (pullF X₀.varpi) Γ) := rho_mk X₀ _ _ _ Γ

def cls (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) : Fin 2 → Q X₀ := fun l => mk X₀ (Γ l)

local notation "𝔻" => DualNumber k

theorem mv_act_cls (N : FormalODModule q 𝔻)
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i)))
    (a : Zp2 q) :
    mv X₀ (MvFormalGroup.linearPart (X₀.act a)) (cls X₀ Γ) = fun l => ρa X₀ a (cls X₀ Γ l) := by
  obtain ⟨g, hg, h⟩ :=
    CerednikDrinfeld.FormalODModule.exists_sum_linearPart_act_smul_eq_subst_act_add_addCoboundary X₀ N hN Γ hΓ hNΓ a
  funext l
  show ∑ i, MvFormalGroup.linearPart (X₀.act a) l i • mk X₀ (Γ i) = ρa X₀ a (mk X₀ (Γ l))
  have e : mk X₀ (∑ i, MvFormalGroup.linearPart (X₀.act a) l i • Γ i) =
      mk X₀ (subst (pullF (X₀.act a)) (Γ l) + X₀.F.addCoboundary (g l)) := congrArg (mk X₀) (h l)
  rw [map_sum] at e
  simp only [map_smul] at e
  rw [e, map_add, mk_addCoboundary X₀ (hg l), add_zero, ρa_mk]

theorem mv_varpi_cls (N : FormalODModule q 𝔻)
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) :
    mv X₀ (MvFormalGroup.linearPart X₀.varpi) (cls X₀ Γ) = fun l => ρv X₀ (cls X₀ Γ l) := by
  obtain ⟨g, hg, h⟩ :=
    CerednikDrinfeld.FormalODModule.exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary X₀ N hN Γ hΓ hNΓ
  funext l
  show ∑ i, MvFormalGroup.linearPart X₀.varpi l i • mk X₀ (Γ i) = ρv X₀ (mk X₀ (Γ l))
  have e : mk X₀ (∑ i, MvFormalGroup.linearPart X₀.varpi l i • Γ i) =
      mk X₀ (subst (pullF X₀.varpi) (Γ l) + X₀.F.addCoboundary (g l)) := congrArg (mk X₀) (h l)
  rw [map_sum] at e
  simp only [map_smul] at e
  rw [e, map_add, mk_addCoboundary X₀ (hg l), add_zero, ρv_mk]

theorem eig_zero {v : Fin 2 → k} (hv : v ∈ X₀.toFormalODModule.lieZero j₀) (a : Zp2 q) :
    (MvFormalGroup.linearPart (X₀.act a)).mulVec v = j₀ a • v := by
  have h : v ∈ ⨅ a : Zp2 q, LinearMap.ker (X₀.toFormalODModule.lieAct a - j₀ a • LinearMap.id) := hv
  rw [Submodule.mem_iInf] at h
  have h' := h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h'
  exact h'

theorem eig_one {v : Fin 2 → k} (hv : v ∈ X₀.toFormalODModule.lieOne j₀) (a : Zp2 q) :
    (MvFormalGroup.linearPart (X₀.act a)).mulVec v = j₀ (WittVector.frobenius a) • v := by
  have h : v ∈ ⨅ a : Zp2 q,
      LinearMap.ker (X₀.toFormalODModule.lieAct a - j₀ (WittVector.frobenius a) • LinearMap.id) := hv
  rw [Submodule.mem_iInf] at h
  have h' := h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h'
  exact h'

theorem exists_eig_zero : ∃ v ∈ X₀.toFormalODModule.lieZero j₀, v ≠ 0 := by
  haveI : Module.Invertible k (X₀.toFormalODModule.lieZero j₀) := X₀.isSpecial.2.1
  have h1 : Module.finrank k (X₀.toFormalODModule.lieZero j₀) = 1 := Module.Invertible.finrank_eq_one k _
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)
    (M := X₀.toFormalODModule.lieZero j₀)).mp (by omega)
  exact ⟨v, v.2, fun h => hv (Subtype.ext h)⟩

theorem exists_eig_one : ∃ v ∈ X₀.toFormalODModule.lieOne j₀, v ≠ 0 := by
  haveI : Module.Invertible k (X₀.toFormalODModule.lieOne j₀) := X₀.isSpecial.2.2
  have h1 : Module.finrank k (X₀.toFormalODModule.lieOne j₀) = 1 := Module.Invertible.finrank_eq_one k _
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)
    (M := X₀.toFormalODModule.lieOne j₀)).mp (by omega)
  exact ⟨v, v.2, fun h => hv (Subtype.ext h)⟩

theorem det_ne_zero {v₀ v₁ : Fin 2 → k} (h₀ : v₀ ∈ X₀.toFormalODModule.lieZero j₀) (hv₀ : v₀ ≠ 0)
    (h₁ : v₁ ∈ X₀.toFormalODModule.lieOne j₀) (hv₁ : v₁ ≠ 0) :
    v₀ 0 * v₁ 1 - v₁ 0 * v₀ 1 ≠ 0 := by
  have hdisj : ∀ w : Fin 2 → k, w ∈ X₀.toFormalODModule.lieZero j₀ → w ∈ X₀.toFormalODModule.lieOne j₀ → w = 0 :=
    fun w hw₀ hw₁ => (Submodule.disjoint_def.mp X₀.isSpecial.1.disjoint) w hw₀ hw₁
  intro hdet

  have hne : v₀ 0 ≠ 0 ∨ v₀ 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv₀ (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
  rcases hne with h0 | h1
  ·
    have hw : (v₀ 0) • v₁ = (v₁ 0) • v₀ := by
      funext i; fin_cases i
      · show v₀ 0 * v₁ 0 = v₁ 0 * v₀ 0; ring
      · show v₀ 0 * v₁ 1 = v₁ 0 * v₀ 1; linear_combination hdet
    have hmem : (v₀ 0) • v₁ ∈ X₀.toFormalODModule.lieZero j₀ := hw ▸ Submodule.smul_mem _ _ h₀
    have hz := hdisj _ hmem (Submodule.smul_mem _ _ h₁)
    exact hv₁ ((smul_eq_zero.mp hz).resolve_left h0)
  · have hw : (v₀ 1) • v₁ = (v₁ 1) • v₀ := by
      funext i; fin_cases i
      · show v₀ 1 * v₁ 0 = v₁ 1 * v₀ 0; linear_combination (-1 : k) * hdet
      · show v₀ 1 * v₁ 1 = v₁ 1 * v₀ 1; ring
    have hmem : (v₀ 1) • v₁ ∈ X₀.toFormalODModule.lieZero j₀ := hw ▸ Submodule.smul_mem _ _ h₀
    have hz := hdisj _ hmem (Submodule.smul_mem _ _ h₁)
    exact hv₁ ((smul_eq_zero.mp hz).resolve_left h1)

theorem linearPart_varpi_sq :
    MvFormalGroup.linearPart X₀.varpi * MvFormalGroup.linearPart X₀.varpi = 0 := by
  have h1 : MvFormalGroup.linearPart (X₀.varpi.comp X₀.varpi) =
      MvFormalGroup.linearPart X₀.varpi * MvFormalGroup.linearPart X₀.varpi :=
    MvFormalGroup.linearPart_subst (varpi_cc X₀) X₀.varpi
  rw [← h1, X₀.varpi_comp_varpi, FormalODModule.act_natCast, MvFormalGroup.linearPart_nthSeries,
    ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]

theorem dep_of_type [IsAlgClosed k] (χ : Zp2 q →+* k)
    {Δ Δ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (hΔ : X₀.F.IsSymmTwoCocycle Δ) (hΔ' : X₀.F.IsSymmTwoCocycle Δ')
    (ht : ∀ a, ρa X₀ a (mk X₀ Δ) = χ a • mk X₀ Δ) (ht' : ∀ a, ρa X₀ a (mk X₀ Δ') = χ a • mk X₀ Δ') :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • mk X₀ Δ + c' • mk X₀ Δ' = 0 := by
  have typ : ∀ {E : MvPowerSeries (Fin 2 ⊕ Fin 2) k}, (∀ a, ρa X₀ a (mk X₀ E) = χ a • mk X₀ E) →
      ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧
        subst (pullF (X₀.act a)) E = χ a • E + X₀.F.addCoboundary g := by
    intro E hE a
    have h := hE a
    rw [ρa_mk, ← map_smul] at h
    exact exists_of_mk_eq X₀ h
  obtain ⟨c, c', g, hcc, hg, hrel⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
      X₀ χ Δ Δ' hΔ hΔ' (typ ht) (typ ht')
  refine ⟨c, c', hcc, ?_⟩
  rw [← map_smul, ← map_smul, ← map_add, hrel]
  exact mk_addCoboundary X₀ hg

theorem exists_generator [IsAlgClosed k] (χ : Zp2 q →+* k) :
    ∃ E : MvPowerSeries (Fin 2 ⊕ Fin 2) k, X₀.F.IsSymmTwoCocycle E ∧
      ∀ Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, X₀.F.IsSymmTwoCocycle Δ →
        (∀ a, ρa X₀ a (mk X₀ Δ) = χ a • mk X₀ Δ) → ∃ c : k, mk X₀ Δ = c • mk X₀ E := by
  classical
  by_cases hex : ∃ E : MvPowerSeries (Fin 2 ⊕ Fin 2) k, X₀.F.IsSymmTwoCocycle E ∧
      (∀ a, ρa X₀ a (mk X₀ E) = χ a • mk X₀ E) ∧ mk X₀ E ≠ 0
  · obtain ⟨E, hE, htE, hE0⟩ := hex
    refine ⟨E, hE, fun Δ hΔ htΔ => ?_⟩
    obtain ⟨c, c', hcc, hrel⟩ := dep_of_type X₀ χ hΔ hE htΔ htE
    by_cases hc : c = 0
    · have hc' : c' ≠ 0 := hcc.resolve_left (not_not_intro hc)
      rw [hc, zero_smul, zero_add] at hrel
      exact absurd ((smul_eq_zero.mp hrel).resolve_left hc') hE0
    · refine ⟨-(c⁻¹ * c'), ?_⟩
      have : mk X₀ Δ = c⁻¹ • (c • mk X₀ Δ) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this, eq_neg_of_add_eq_zero_left hrel, smul_neg, smul_smul, neg_smul]
  · refine ⟨0, MvFormalGroup.IsSymmTwoCocycle.zero _, fun Δ hΔ htΔ => ⟨0, ?_⟩⟩
    push_neg at hex
    rw [hex Δ hΔ htΔ, zero_smul]

end asm

end CLineAsm
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and.CLineAsm"

namespace CLineAsm

section fin

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule
open MvPowerSeries (subst constantCoeff)

variable {q : ℕ} [Fact q.Prime]
variable {k : Type u} [Field k] [CharP k q] [IsAlgClosed k] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

local notation "𝔻" => DualNumber k

theorem main
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ Γ₁ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k, (∀ l, X₀.F.IsSymmTwoCocycle (Γ₁ l)) ∧
      ∀ (N : FormalODModule q 𝔻),
        N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule →
      ∀ (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k), (∀ l, X₀.F.IsSymmTwoCocycle (Γ l)) →
        (∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) →
        ∃ (c : k) (g : Fin 2 → MvPowerSeries (Fin 2) k),
          (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
          ∀ l, Γ l = c • Γ₁ l + X₀.F.addCoboundary (g l) := by
  classical

  obtain ⟨v₀, hv₀m, hv₀⟩ := exists_eig_zero X₀
  obtain ⟨v₁, hv₁m, hv₁⟩ := exists_eig_one X₀
  have hdet := det_ne_zero X₀ hv₀m hv₀ hv₁m hv₁
  set d : k := v₀ 0 * v₁ 1 - v₁ 0 * v₀ 1 with hd
  set P : Matrix (Fin 2) (Fin 2) k := Matrix.of (fun r c => (![v₀ r, v₁ r] : Fin 2 → k) c) with hP
  set Pi : Matrix (Fin 2) (Fin 2) k := !![d⁻¹ * v₁ 1, -(d⁻¹ * v₁ 0); -(d⁻¹ * v₀ 1), d⁻¹ * v₀ 0] with hPi
  have hPPi : P * Pi = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hP, hPi, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hPiP : Pi * P = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hP, hPi, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

  let χ₁ : Zp2 q →+* k := j₀.comp (WittVector.frobenius (p := q) (R := GaloisField q 2))
  set D : Zp2 q → Matrix (Fin 2) (Fin 2) k := fun a => !![j₀ a, 0; 0, χ₁ a] with hD
  have hlamP : ∀ a, MvFormalGroup.linearPart (X₀.act a) * P = P * D a := by
    intro a
    have e0 := eig_zero X₀ hv₀m a
    have e1 := eig_one X₀ hv₁m a
    have e0' : ∀ i, MvFormalGroup.linearPart (X₀.act a) i 0 * v₀ 0 +
        MvFormalGroup.linearPart (X₀.act a) i 1 * v₀ 1 = j₀ a * v₀ i := fun i => by
      have := congrFun e0 i
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have e1' : ∀ i, MvFormalGroup.linearPart (X₀.act a) i 0 * v₁ 0 +
        MvFormalGroup.linearPart (X₀.act a) i 1 * v₁ 1 = χ₁ a * v₁ i := fun i => by
      have := congrFun e1 i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      exact this
    ext i j
    fin_cases j
    · simp [hP, hD, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination e0' i
    · simp [hP, hD, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination e1' i

  set L : Matrix (Fin 2) (Fin 2) k := MvFormalGroup.linearPart X₀.varpi with hL
  set B : Matrix (Fin 2) (Fin 2) k := Pi * L * P with hB
  have hB2 : B * B = 0 := by
    have hL2 : L * L = 0 := linearPart_varpi_sq X₀
    calc B * B = Pi * L * (P * Pi) * L * P := by simp only [hB, Matrix.mul_assoc]
      _ = 0 := by rw [hPPi, Matrix.mul_one, Matrix.mul_assoc Pi L L, hL2, Matrix.mul_zero, Matrix.zero_mul]
  have hLB : L = P * B * Pi := by
    calc L = (P * Pi) * L * (P * Pi) := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = P * B * Pi := by simp only [hB, Matrix.mul_assoc]
  have hBne : B ≠ 0 := by
    intro hB0
    have hL0 : L = 0 := by rw [hLB, hB0, Matrix.mul_zero, Matrix.zero_mul]
    exact hsmooth ⟨fun m _ => by rw [Matrix.mulVecLin_apply, hL0, Matrix.zero_mulVec],
      fun m _ => by rw [Matrix.mulVecLin_apply, hL0, Matrix.zero_mulVec]⟩
  have hoff : B 0 1 ≠ 0 ∨ B 1 0 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h00 : B 0 0 * B 0 0 = 0 := by
      have := congrFun (congrFun hB2 0) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, hc.1, zero_mul, add_zero] at this
      exact this
    have h11 : B 1 1 * B 1 1 = 0 := by
      have := congrFun (congrFun hB2 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, hc.2, zero_mul, zero_add] at this
      exact this
    apply hBne
    ext i j; fin_cases i <;> fin_cases j
    · exact mul_self_eq_zero.mp h00
    · exact hc.1
    · exact hc.2
    · exact mul_self_eq_zero.mp h11

  have coords : ∀ (N : FormalODModule q 𝔻),
      N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule →
      ∀ (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k), (∀ l, X₀.F.IsSymmTwoCocycle (Γ l)) →
        (∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) →
        let y := mv X₀ Pi (cls X₀ Γ)
        (∀ a, ρa X₀ a (y 0) = j₀ a • y 0) ∧ (∀ a, ρa X₀ a (y 1) = χ₁ a • y 1) ∧
        (B 0 0 • y 0 + B 0 1 • y 1 = ρv X₀ (y 0)) ∧ (B 1 0 • y 0 + B 1 1 • y 1 = ρv X₀ (y 1)) ∧
        cls X₀ Γ = mv X₀ P y := by
    intro N hN Γ hΓ hNΓ
    have hact := mv_act_cls X₀ N hN Γ hΓ hNΓ
    have hvar := mv_varpi_cls X₀ N hN Γ hΓ hNΓ

    have hDy : ∀ a, (fun l => ρa X₀ a (mv X₀ Pi (cls X₀ Γ) l)) = mv X₀ (D a) (mv X₀ Pi (cls X₀ Γ)) := by
      intro a
      have hPilam : Pi * MvFormalGroup.linearPart (X₀.act a) = D a * Pi := by
        calc Pi * MvFormalGroup.linearPart (X₀.act a)
            = Pi * MvFormalGroup.linearPart (X₀.act a) * (P * Pi) := by rw [hPPi, Matrix.mul_one]
          _ = Pi * (MvFormalGroup.linearPart (X₀.act a) * P) * Pi := by simp only [Matrix.mul_assoc]
          _ = Pi * (P * D a) * Pi := by rw [hlamP a]
          _ = (Pi * P) * D a * Pi := by simp only [Matrix.mul_assoc]
          _ = D a * Pi := by rw [hPiP, Matrix.one_mul]
      rw [map_mv, ← hact, mv_mv, mv_mv, hPilam]
    have hBy : (fun l => ρv X₀ (mv X₀ Pi (cls X₀ Γ) l)) = mv X₀ B (mv X₀ Pi (cls X₀ Γ)) := by
      have hPiL : Pi * L = B * Pi := by
        calc Pi * L = Pi * L * (P * Pi) := by rw [hPPi, Matrix.mul_one]
          _ = B * Pi := by simp only [hB, Matrix.mul_assoc]
      rw [map_mv, ← hvar, mv_mv, mv_mv, ← hL, hPiL]
    refine ⟨fun a => ?_, fun a => ?_, ?_, ?_, ?_⟩
    · have := congrFun (hDy a) 0
      rw [this, mv_apply X₀ (D a)]; simp [hD]
    · have := congrFun (hDy a) 1
      rw [this, mv_apply X₀ (D a)]; simp [hD]
    · have := congrFun hBy 0
      rw [this, mv_apply X₀ B]
    · have := congrFun hBy 1
      rw [this, mv_apply X₀ B]
    · rw [mv_mv, hPPi, mv_one]

  have repY : ∀ (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k), (∀ l, X₀.F.IsSymmTwoCocycle (Γ l)) →
      ∀ l, mv X₀ Pi (cls X₀ Γ) l = mk X₀ (Pi l 0 • Γ 0 + Pi l 1 • Γ 1) ∧
        X₀.F.IsSymmTwoCocycle (Pi l 0 • Γ 0 + Pi l 1 • Γ 1) := fun Γ hΓ l =>
    ⟨by rw [mv_apply, map_add, map_smul, map_smul]; rfl,
     isSymmTwoCocycle_add (isSymmTwoCocycle_smul _ (hΓ 0)) (isSymmTwoCocycle_smul _ (hΓ 1))⟩

  obtain ⟨E₀, hE₀, hgen₀⟩ := exists_generator X₀ j₀
  obtain ⟨E₁, hE₁, hgen₁⟩ := exists_generator X₀ χ₁
  rcases hoff with h01 | h10
  ·
    obtain ⟨F₀, hF₀⟩ : ∃ F₀ : MvPowerSeries (Fin 2 ⊕ Fin 2) k,
        F₀ = (B 0 1)⁻¹ • (subst (pullF X₀.varpi) E₀ - B 0 0 • E₀) := ⟨_, rfl⟩
    have hF₀c : X₀.F.IsSymmTwoCocycle F₀ := by
      have h := isSymmTwoCocycle_add (hZ_varpi X₀ E₀ hE₀) (isSymmTwoCocycle_smul (-(B 0 0)) hE₀)
      rw [neg_smul, ← sub_eq_add_neg] at h
      rw [hF₀]; exact isSymmTwoCocycle_smul _ h
    have hF₀mk : mk X₀ F₀ = (B 0 1)⁻¹ • (ρv X₀ (mk X₀ E₀) - B 0 0 • mk X₀ E₀) := by
      rw [hF₀, map_smul, map_sub, map_smul, ρv_mk]
    refine ⟨fun l => P l 0 • E₀ + P l 1 • F₀,
      fun l => isSymmTwoCocycle_add (isSymmTwoCocycle_smul _ hE₀) (isSymmTwoCocycle_smul _ hF₀c), ?_⟩
    intro N hN Γ hΓ hNΓ
    obtain ⟨ht0, -, hb0, -, hx⟩ := coords N hN Γ hΓ hNΓ
    obtain ⟨hy0, hY0c⟩ := repY Γ hΓ 0

    obtain ⟨c, hc⟩ := hgen₀ _ hY0c (fun a => by rw [← hy0]; exact ht0 a)
    rw [← hy0] at hc
    have hy1 : mv X₀ Pi (cls X₀ Γ) 1 = c • mk X₀ F₀ := by
      have e : mv X₀ Pi (cls X₀ Γ) 1 =
          (B 0 1)⁻¹ • (ρv X₀ (mv X₀ Pi (cls X₀ Γ) 0) - B 0 0 • mv X₀ Pi (cls X₀ Γ) 0) := by
        rw [← hb0, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h01, one_smul]
      rw [e, hc, hF₀mk, map_smul]
      module
    refine ⟨c, ?_⟩
    have key : ∀ l, mk X₀ (Γ l) = mk X₀ (c • (P l 0 • E₀ + P l 1 • F₀)) := by
      intro l
      have := congrFun hx l
      change mk X₀ (Γ l) = mv X₀ P (mv X₀ Pi (cls X₀ Γ)) l at this
      rw [this, mv_apply X₀ P, hc, hy1]
      simp only [map_smul, map_add]
      module
    have key' : ∀ l, ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧
        Γ l = c • (P l 0 • E₀ + P l 1 • F₀) + X₀.F.addCoboundary g := fun l => exists_of_mk_eq X₀ (key l)
    choose g hg hrel using key'
    exact ⟨g, hg, hrel⟩
  ·
    obtain ⟨F₁, hF₁⟩ : ∃ F₁ : MvPowerSeries (Fin 2 ⊕ Fin 2) k,
        F₁ = (B 1 0)⁻¹ • (subst (pullF X₀.varpi) E₁ - B 1 1 • E₁) := ⟨_, rfl⟩
    have hF₁c : X₀.F.IsSymmTwoCocycle F₁ := by
      have h := isSymmTwoCocycle_add (hZ_varpi X₀ E₁ hE₁) (isSymmTwoCocycle_smul (-(B 1 1)) hE₁)
      rw [neg_smul, ← sub_eq_add_neg] at h
      rw [hF₁]; exact isSymmTwoCocycle_smul _ h
    have hF₁mk : mk X₀ F₁ = (B 1 0)⁻¹ • (ρv X₀ (mk X₀ E₁) - B 1 1 • mk X₀ E₁) := by
      rw [hF₁, map_smul, map_sub, map_smul, ρv_mk]
    refine ⟨fun l => P l 0 • F₁ + P l 1 • E₁,
      fun l => isSymmTwoCocycle_add (isSymmTwoCocycle_smul _ hF₁c) (isSymmTwoCocycle_smul _ hE₁), ?_⟩
    intro N hN Γ hΓ hNΓ
    obtain ⟨-, ht1, -, hb1, hx⟩ := coords N hN Γ hΓ hNΓ
    obtain ⟨hy1r, hY1c⟩ := repY Γ hΓ 1
    obtain ⟨c, hc⟩ := hgen₁ _ hY1c (fun a => by rw [← hy1r]; exact ht1 a)
    rw [← hy1r] at hc
    have hy0 : mv X₀ Pi (cls X₀ Γ) 0 = c • mk X₀ F₁ := by
      have e : mv X₀ Pi (cls X₀ Γ) 0 =
          (B 1 0)⁻¹ • (ρv X₀ (mv X₀ Pi (cls X₀ Γ) 1) - B 1 1 • mv X₀ Pi (cls X₀ Γ) 1) := by
        rw [← hb1, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h10, one_smul]
      rw [e, hc, hF₁mk, map_smul]
      module
    refine ⟨c, ?_⟩
    have key : ∀ l, mk X₀ (Γ l) = mk X₀ (c • (P l 0 • F₁ + P l 1 • E₁)) := by
      intro l
      have := congrFun hx l
      change mk X₀ (Γ l) = mv X₀ P (mv X₀ Pi (cls X₀ Γ)) l at this
      rw [this, mv_apply X₀ P, hy0, hc]
      simp only [map_smul, map_add]
      module
    have key' : ∀ l, ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧
        Γ l = c • (P l 0 • F₁ + P l 1 • E₁) + X₀.F.addCoboundary g := fun l => exists_of_mk_eq X₀ (key l)
    choose g hg hrel using key'
    exact ⟨g, hg, hrel⟩

end fin
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and.CLineAsm"

end CLineAsm
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and.CLineAsm"

open CLineAsm CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ Γ₁ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k, (∀ l, X₀.F.IsSymmTwoCocycle (Γ₁ l)) ∧
      ∀ (N : FormalODModule q (DualNumber k)),
        N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule →
      ∀ (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k), (∀ l, X₀.F.IsSymmTwoCocycle (Γ l)) →
        (∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) →
        ∃ (c : k) (g : Fin 2 → MvPowerSeries (Fin 2) k),
          (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
          ∀ l, Γ l = c • Γ₁ l + X₀.F.addCoboundary (g l) :=
  CLineAsm.main X₀ hsmooth

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and.CLineAsm"

end S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and (solution)
