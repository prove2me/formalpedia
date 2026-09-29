-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4b58890b-74ba-5705-9d48-984d5da91ea6

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
import Theorems.Thm_MvFormalGroup_Hom_eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow
import Theorems.Thm_MvFormalGroup_translate_injective_and_exists_hom_iff_exists_addCoboundary
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

noncomputable section

namespace F3bCoreAsm

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

variable (X₀) in

theorem linearPart_varpi_eq_zero
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) :
    MvFormalGroup.linearPart X₀.varpi = 0 := by
  have htop : X₀.toFormalODModule.lieZero j₀ ⊔ X₀.toFormalODModule.lieOne j₀ = ⊤ := X₀.isSpecial.1.sup_eq_top
  have hall : ∀ m : Fin 2 → k, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0 := by
    intro m
    have hm : m ∈ X₀.toFormalODModule.lieZero j₀ ⊔ X₀.toFormalODModule.lieOne j₀ := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
    rw [map_add, hnode₀ y hy, hnode₁ z hz, add_zero]
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have h := hall (Pi.single i 1)
  rw [Matrix.mulVecLin_apply] at h
  rw [h, Matrix.zero_mulVec]

def pullF (φ : Series k) : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  Sum.elim
    (fun i => subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
    fun i => subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i)

theorem pullF_cc {φ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) (s : Fin 2 ⊕ Fin 2) :
    constantCoeff (pullF φ s) = 0 := by
  rcases s with i | i
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)
      (fun m => constantCoeff_X _) (hφ i)
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)
      (fun m => constantCoeff_X _) (hφ i)

theorem hasSubst_pullF {φ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) : HasSubst (pullF φ) :=
  hasSubst_of_constantCoeff_zero (pullF_cc hφ)

theorem isSymmTwoCocycle_sub {Γ₁ Γ₂ : MvPowerSeries (Fin 2 ⊕ Fin 2) k}
    (h₁ : X₀.F.IsSymmTwoCocycle Γ₁) (h₂ : X₀.F.IsSymmTwoCocycle Γ₂) : X₀.F.IsSymmTwoCocycle (Γ₁ - Γ₂) := by
  have h := isSymmTwoCocycle_add h₁ (isSymmTwoCocycle_smul (-1) h₂)
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

theorem exists_coc_eq_add_of_linearPart_eq [IsAlgClosed k]
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    {N₁ N₂ : FormalODModule q 𝔻} (h₁ : IsNose X₀ N₁) (h₂ : IsNose X₀ N₂)
    (hvarpi : MvFormalGroup.linearPart N₁.varpi = MvFormalGroup.linearPart N₂.varpi) :
    ∃ b : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, constantCoeff (b l) = 0) ∧
      ∀ l, coc h₂ l = coc h₁ l + X₀.F.addCoboundary (b l) := by
  have hlam := linearPart_varpi_eq_zero X₀ hnode₀ hnode₁
  have hvcc : ∀ i, constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1
  obtain ⟨g₁, hg₁, hrel₁, hlin₁⟩ :=
    CerednikDrinfeld.FormalODModule.exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart
      X₀ N₁ h₁ (coc h₁) (coc_isCocycle h₁) (toPowerSeries_eq_T h₁)
  obtain ⟨g₂, hg₂, hrel₂, hlin₂⟩ :=
    CerednikDrinfeld.FormalODModule.exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart
      X₀ N₂ h₂ (coc h₂) (coc_isCocycle h₂) (toPowerSeries_eq_T h₂)
  have key : ∀ l, ∃ b : MvPowerSeries (Fin 2) k, constantCoeff b = 0 ∧
      coc h₂ l = coc h₁ l + X₀.F.addCoboundary b := by
    intro l
    have e₁ : subst (pullF X₀.varpi) (coc h₁ l) = X₀.F.addCoboundary (g₁ l) := by
      have h := hrel₁ l
      simp only [hlam, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at h
      exact h
    have e₂ : subst (pullF X₀.varpi) (coc h₂ l) = X₀.F.addCoboundary (g₂ l) := by
      have h := hrel₂ l
      simp only [hlam, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at h
      exact h
    have hγ : X₀.F.IsSymmTwoCocycle (coc h₂ l - coc h₁ l) :=
      isSymmTwoCocycle_sub (coc_isCocycle h₂ l) (coc_isCocycle h₁ l)
    have hpull : subst (pullF X₀.varpi) (coc h₂ l - coc h₁ l) = X₀.F.addCoboundary (g₂ l - g₁ l) := by
      rw [MvPowerSeries.subst_sub (hasSubst_pullF hvcc), e₁, e₂, sub_eq_add_neg (g₂ l), addCoboundary_add,
        addCoboundary_neg, ← sub_eq_add_neg]
    have hcc : constantCoeff (g₂ l - g₁ l) = 0 := by rw [map_sub, hg₁, hg₂, sub_zero]
    have hlin0 : ∀ m, MvPowerSeries.coeff (Finsupp.single m 1) (g₂ l - g₁ l) = 0 := fun m => by
      rw [map_sub, hlin₁ l m, hlin₂ l m, hvarpi, sub_self]
    obtain ⟨b, hb0, hb⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
        X₀ hnode₀ hnode₁ (coc h₂ l - coc h₁ l) hγ (g₂ l - g₁ l) hcc hlin0 hpull
    exact ⟨b, hb0, by rw [← hb]; ring⟩
  choose b hb0 hb using key
  exact ⟨b, hb0, hb⟩

end nose

end F3bCoreAsm
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq.F3bCoreAsm"

open F3bCoreAsm CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (N N' : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (hN' : N'.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (hvarpi : MvFormalGroup.linearPart N.varpi = MvFormalGroup.linearPart N'.varpi) :
    ∃ θ : N.Hom N', θ.IsIso ∧ θ.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom = Series.id k := by
  obtain ⟨b, hb0, hb⟩ := F3bCoreAsm.exists_coc_eq_add_of_linearPart_eq (X₀ := X₀) hnode₀ hnode₁ hN hN' hvarpi
  obtain ⟨v, hv, hvk⟩ := F3bCoreAsm.exists_iso_of_coc_eq_add hN hN' b hb0 hb
  exact ⟨v, hv, hvk⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq.F3bCoreAsm"

end S_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq (solution)
