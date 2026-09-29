-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/090f075a-8300-5e7e-929a-e396bebe30b2

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective
import Theorems.Thm_MvFormalGroup_Hom_eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

noncomputable section

namespace R4ODGlue

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

theorem inverse_unique {s g₁ g₂ : Series A} (hs : ∀ i, constantCoeff (s i) = 0)
    (hg₂ : ∀ i, constantCoeff (g₂ i) = 0)
    (h₁ : g₁.comp s = Series.id A) (h₂ : s.comp g₂ = Series.id A) : g₁ = g₂ := by
  calc g₁ = g₁.comp (Series.id A) := (Series.comp_id _).symm
    _ = g₁.comp (s.comp g₂) := by rw [h₂]
    _ = (g₁.comp s).comp g₂ := (Series.comp_assoc _ _ _ hs hg₂).symm
    _ = g₂ := by rw [h₁, Series.id_comp _ hg₂]

end homs

section lawhoms

variable {A : Type u} [CommRing A]

open MvFormalGroup in
theorem lawcomp_toPowerSeries {F G H : MvFormalGroup 2 A} (ψ : G.Hom H) (φ : F.Hom G) :
    (ψ.comp φ).toPowerSeries = Series.comp ψ.toPowerSeries φ.toPowerSeries := rfl

open MvFormalGroup in
theorem lawid_toPowerSeries (F : MvFormalGroup 2 A) :
    (MvFormalGroup.Hom.id F).toPowerSeries = Series.id A := rfl

theorem hom_subst_elim {g h : ℕ} (F : MvFormalGroup g A) (G : MvFormalGroup h A) (φ : F.Hom G)
    {τ : Type*} {a b : Fin g → MvPowerSeries τ A} (ha : ∀ j, (a j).constantCoeff = 0)
    (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin h) :
    subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (φ.toPowerSeries i) =
      subst (Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j))
        (G.toPowerSeries i) := by
  have hab : HasSubst (Sum.elim a b) := MvFormalGroup.hasSubst_elim ha hb
  have hXl : HasSubst (fun l : Fin g =>
      (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) A)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin g =>
      (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) A)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hA : HasSubst (Sum.elim
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) A))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) A))
        (φ.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j) <;>
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
  have key := congrArg (subst (Sum.elim a b)) (φ.subst_eq i)
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab, subst_comp_subst_apply hA hab] at key
  have hfam : (fun s => subst (Sum.elim a b) ((Sum.elim
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) A))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) A))
        (φ.toPowerSeries j)) s))
      = Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a b) (subst (fun l =>
          (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) A))
          (φ.toPowerSeries j)) = subst a (φ.toPowerSeries j)
      rw [subst_comp_subst_apply hXl hab]
      congr 1
      funext l
      exact subst_X hab (Sum.inl l)
    · show subst (Sum.elim a b) (subst (fun l =>
          (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) A))
          (φ.toPowerSeries j)) = subst b (φ.toPowerSeries j)
      rw [subst_comp_subst_apply hXr hab]
      congr 1
      funext l
      exact subst_X hab (Sum.inr l)
  rw [hfam] at key
  exact key

theorem addVia_comp (G : MvFormalGroup 2 A) (u v Φ : Series A) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (hΦ : ∀ i, constantCoeff (Φ i) = 0) :
    (Series.addVia G u v).comp Φ = Series.addVia G (u.comp Φ) (v.comp Φ) := by
  funext i
  show subst Φ (subst (Sum.elim u v) (G.toPowerSeries i)) =
    subst (Sum.elim (u.comp Φ) (v.comp Φ)) (G.toPowerSeries i)
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hu hv) (hasSubst_of_constantCoeff_zero hΦ)]
  congr 1
  funext s
  rcases s with j | j <;> rfl

theorem comp_addVia {F G : MvFormalGroup 2 A} (Ψ : F.Hom G) (u v : Series A)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    Series.comp Ψ.toPowerSeries (Series.addVia F u v) =
      Series.addVia G (Series.comp Ψ.toPowerSeries u) (Series.comp Ψ.toPowerSeries v) := by
  funext i
  exact hom_subst_elim F G Ψ hu hv i

end lawhoms

section height

variable {k : Type u} [Field k]

theorem subst_mem_span_comp (φ θ : Series k) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (f : MvPowerSeries (Fin 2) k) (hf : f ∈ Ideal.span (Set.range θ)) :
    subst φ f ∈ Ideal.span (Set.range (θ.comp φ)) := by
  have hs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  let T : MvPowerSeries (Fin 2) k →ₐ[k] MvPowerSeries (Fin 2) k := MvPowerSeries.substAlgHom hs
  have hT : ∀ g, T g = subst φ g := fun g => by
    show MvPowerSeries.substAlgHom hs g = subst φ g
    rw [← MvPowerSeries.coe_substAlgHom hs]
  have hmap : Ideal.map T (Ideal.span (Set.range θ)) = Ideal.span (Set.range (θ.comp φ)) := by
    rw [Ideal.map_span]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hT (θ i)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨θ i, ⟨i, rfl⟩, hT (θ i)⟩
  rw [← hT, ← hmap]
  exact Ideal.mem_map_of_mem _ hf

theorem subst_span_le (φ θ θ₀ : Series k) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hθ : ∀ i, constantCoeff (θ i) = 0) (hcomm : θ₀.comp φ = φ.comp θ)
    (f : MvPowerSeries (Fin 2) k) (hf : f ∈ Ideal.span (Set.range θ₀)) :
    subst φ f ∈ Ideal.span (Set.range θ) := by
  have h1 := subst_mem_span_comp φ θ₀ hφ f hf
  rw [hcomm] at h1

  have hle : Ideal.span (Set.range (φ.comp θ)) ≤ Ideal.span (Set.range θ) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : φ i ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k)) := by
      rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff 2, RingHom.mem_ker]
      exact hφ i
    have h2 := subst_mem_span_comp θ (fun j => MvPowerSeries.X j) hθ (φ i) hmem
    have hid : (Series.comp (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin 2) k)) θ) = θ :=
      Series.id_comp θ hθ
    rw [hid] at h2
    exact h2
  exact hle h1

theorem finrank_kerAlgebra_eq (φ ψ θ θ₀ : Series k) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hψ : ∀ i, constantCoeff (ψ i) = 0) (hθ : ∀ i, constantCoeff (θ i) = 0)
    (hθ₀ : ∀ i, constantCoeff (θ₀ i) = 0)
    (h₁ : ψ.comp φ = Series.id k) (h₂ : φ.comp ψ = Series.id k)
    (hcomm : θ₀.comp φ = φ.comp θ) :
    Module.finrank k (KerAlgebra θ) = Module.finrank k (KerAlgebra θ₀) := by
  have hsφ : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  have hsψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ

  have hcomm' : θ.comp ψ = ψ.comp θ₀ := by
    have e1 : ψ.comp (θ₀.comp φ) = ψ.comp (φ.comp θ) := by rw [hcomm]
    rw [← Series.comp_assoc _ _ _ hθ₀ hφ, ← Series.comp_assoc _ _ _ hφ hθ, h₁,
      Series.id_comp _ hθ] at e1

    calc θ.comp ψ = ((ψ.comp θ₀).comp φ).comp ψ := by rw [e1]
      _ = (ψ.comp θ₀).comp (φ.comp ψ) :=
          Series.comp_assoc _ _ _ hφ hψ
      _ = ψ.comp θ₀ := by rw [h₂, Series.comp_id]
  let T : MvPowerSeries (Fin 2) k →ₐ[k] MvPowerSeries (Fin 2) k := MvPowerSeries.substAlgHom hsφ
  let U : MvPowerSeries (Fin 2) k →ₐ[k] MvPowerSeries (Fin 2) k := MvPowerSeries.substAlgHom hsψ
  have hT : ∀ g, T g = subst φ g := fun g => by
    show MvPowerSeries.substAlgHom hsφ g = subst φ g
    rw [← MvPowerSeries.coe_substAlgHom hsφ]
  have hU : ∀ g, U g = subst ψ g := fun g => by
    show MvPowerSeries.substAlgHom hsψ g = subst ψ g
    rw [← MvPowerSeries.coe_substAlgHom hsψ]
  have hTU : ∀ g, T (U g) = g := by
    intro g
    rw [hT, hU, subst_comp_subst_apply hsψ hsφ]
    have : (fun j => subst φ (ψ j)) = Series.id k := h₁
    rw [this]
    exact congrFun MvPowerSeries.subst_self g
  have hUT : ∀ g, U (T g) = g := by
    intro g
    rw [hT, hU, subst_comp_subst_apply hsφ hsψ]
    have : (fun j => subst ψ (φ j)) = Series.id k := h₂
    rw [this]
    exact congrFun MvPowerSeries.subst_self g
  let E : MvPowerSeries (Fin 2) k ≃ₐ[k] MvPowerSeries (Fin 2) k :=
    AlgEquiv.ofAlgHom T U (AlgHom.ext hTU) (AlgHom.ext hUT)
  have hE : ∀ g, E g = subst φ g := hT
  have hmap : Ideal.span (Set.range θ) = (Ideal.span (Set.range θ₀)).map (E : _ →+* _) := by
    apply le_antisymm
    · intro f hf
      have hf' : U f ∈ Ideal.span (Set.range θ₀) := by
        rw [hU]
        exact subst_span_le ψ θ₀ θ hψ hθ₀ hcomm' f hf
      have : f = E (U f) := (hTU f).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ hf'
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      show E f ∈ _
      rw [hE]
      exact subst_span_le φ θ θ₀ hφ hθ hcomm f hf
  exact ((Ideal.quotientEquivAlg (Ideal.span (Set.range θ₀)) (Ideal.span (Set.range θ)) E
    hmap).toLinearEquiv.finrank_eq).symm

theorem finrank_of_iso {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (X : FormalODModule q k) (u : X.Hom X₀.toFormalODModule) (hu : u.IsIso) :
    Module.finrank k (MvPowerSeries (Fin 2) k ⧸
      Ideal.span (Set.range (X.F.nthSeries q))) = q ^ 4 := by
  obtain ⟨g, hg₁, hg₂⟩ := hu
  obtain ⟨-, -, hrank⟩ := X₀.hasHeight
  have h0 := hrank k (RingHom.id k)
  rw [Series.map_ringHom_id] at h0
  rw [← FormalODModule.act_natCast]
  have e1 := congrArg FormalODModule.Hom.toSeries hg₁
  have e2 := congrArg FormalODModule.Hom.toSeries hg₂
  simp only [comp_toSeries, id_toSeries] at e1 e2
  have hc : (X₀.act (q : Zp2 q)).comp u.toSeries = u.toSeries.comp (X.act (q : Zp2 q)) :=
    (u.isODHom.2.1 (q : Zp2 q)).symm
  have := finrank_kerAlgebra_eq u.toSeries g.toSeries (X.act (q : Zp2 q))
    (X₀.act (q : Zp2 q)) (hom_cc u) (hom_cc g) (X.isLawHom_act _).1
    (X₀.isLawHom_act _).1 e1 e2 hc
  exact this.trans h0

end height

section transport

variable {C : Type u} [CommRing C]

private def _root_.R4ODGlue.trans (Φ Ψ e : Series C) : Series C := Ψ.comp (e.comp Φ)

p2m_export "R4ODGlue" "trans"
variable {Φ Ψ : Series C} (hΦ : ∀ i, constantCoeff (Φ i) = 0) (hΨ : ∀ i, constantCoeff (Ψ i) = 0)
  (hΨΦ : Ψ.comp Φ = Series.id C) (hΦΨ : Φ.comp Ψ = Series.id C)

theorem cc_comp {a b : Series C} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    ∀ i, constantCoeff ((a.comp b) i) = 0 :=
  Series.constantCoeff_comp ha hb

include hΦ hΨ in
theorem cc_trans {e : Series C} (he : ∀ i, constantCoeff (e i) = 0) :
    ∀ i, constantCoeff (trans Φ Ψ e i) = 0 :=
  cc_comp hΨ (cc_comp he hΦ)

include hΦ hΨΦ in
theorem trans_id : trans Φ Ψ (Series.id C) = Series.id C := by
  rw [trans, Series.id_comp _ hΦ, hΨΦ]

include hΦ hΨ hΦΨ in
theorem trans_comp {e₁ e₂ : Series C} (he₁ : ∀ i, constantCoeff (e₁ i) = 0)
    (he₂ : ∀ i, constantCoeff (e₂ i) = 0) :
    trans Φ Ψ (e₁.comp e₂) = (trans Φ Ψ e₁).comp (trans Φ Ψ e₂) := by
  simp only [trans]
  rw [Series.comp_assoc Ψ (e₁.comp Φ) (Ψ.comp (e₂.comp Φ)) (cc_comp he₁ hΦ)
      (cc_comp hΨ (cc_comp he₂ hΦ)),
    Series.comp_assoc e₁ Φ (Ψ.comp (e₂.comp Φ)) hΦ (cc_comp hΨ (cc_comp he₂ hΦ)),
    ← Series.comp_assoc Φ Ψ (e₂.comp Φ) hΨ (cc_comp he₂ hΦ), hΦΨ,
    Series.id_comp _ (cc_comp he₂ hΦ), Series.comp_assoc e₁ e₂ Φ he₂ hΦ]

include hΦ hΨ hΦΨ in

theorem comp_trans {e : Series C} (he : ∀ i, constantCoeff (e i) = 0) :
    Φ.comp (trans Φ Ψ e) = e.comp Φ := by
  rw [trans, ← Series.comp_assoc Φ Ψ (e.comp Φ) hΨ (cc_comp he hΦ), hΦΨ,
    Series.id_comp _ (cc_comp he hΦ)]

include hΦ hΨ hΦΨ in

theorem trans_comp_inv {e : Series C} (he : ∀ i, constantCoeff (e i) = 0) :
    (trans Φ Ψ e).comp Ψ = Ψ.comp e := by
  rw [trans, Series.comp_assoc Ψ (e.comp Φ) Ψ (cc_comp he hΦ) hΨ,
    Series.comp_assoc e Φ Ψ hΦ hΨ, hΦΨ, Series.comp_id]

theorem isLawHom_trans {F'' G'' : MvFormalGroup 2 C} (Φh : G''.Hom F'') (Ψh : F''.Hom G'')
    {e : Series C} (he : IsLawHom F'' F'' e) :
    IsLawHom G'' G'' (trans Φh.toPowerSeries Ψh.toPowerSeries e) :=
  IsLawHom.of_hom (Ψh.comp (he.toHom.comp Φh))

theorem trans_addVia {F'' G'' : MvFormalGroup 2 C} (Φh : G''.Hom F'') (Ψh : F''.Hom G'')
    {e₁ e₂ : Series C} (he₁ : ∀ i, constantCoeff (e₁ i) = 0) (he₂ : ∀ i, constantCoeff (e₂ i) = 0) :
    trans Φh.toPowerSeries Ψh.toPowerSeries (Series.addVia F'' e₁ e₂) =
      Series.addVia G'' (trans Φh.toPowerSeries Ψh.toPowerSeries e₁)
        (trans Φh.toPowerSeries Ψh.toPowerSeries e₂) := by
  simp only [trans]
  rw [addVia_comp F'' e₁ e₂ Φh.toPowerSeries he₁ he₂ Φh.constantCoeff_eq_zero,
    comp_addVia Ψh _ _ (cc_comp he₁ Φh.constantCoeff_eq_zero) (cc_comp he₂ Φh.constantCoeff_eq_zero)]

theorem map_trans {C' : Type u} [CommRing C'] (f : C →+* C') {e : Series C}
    (he : ∀ i, constantCoeff (e i) = 0) (hΦ : ∀ i, constantCoeff (Φ i) = 0) :
    (trans Φ Ψ e).map f = trans (Φ.map f) (Ψ.map f) (e.map f) := by
  rw [trans, trans, Series.map_comp f _ _ (cc_comp he hΦ), Series.map_comp f _ _ hΦ]

theorem isComm_of_hom {F'' G'' : MvFormalGroup 2 C} [F''.IsComm] (Φh : G''.Hom F'') (Ψh : F''.Hom G'')
    (h : Series.comp Ψh.toPowerSeries Φh.toPowerSeries = Series.id C) : G''.IsComm := by

  have hΦc : ∀ i, constantCoeff (Φh.toPowerSeries i) = 0 := Φh.constantCoeff_eq_zero
  have hΨc : ∀ i, constantCoeff (Ψh.toPowerSeries i) = 0 := Ψh.constantCoeff_eq_zero
  let XL : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) C := fun l => MvPowerSeries.X (Sum.inl l)
  let XR : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) C := fun l => MvPowerSeries.X (Sum.inr l)
  have hXL : ∀ l, constantCoeff (XL l) = 0 := fun l => constantCoeff_X _
  have hXR : ∀ l, constantCoeff (XR l) = 0 := fun l => constantCoeff_X _
  let ΦL : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) C := fun j => subst XL (Φh.toPowerSeries j)
  let ΦR : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) C := fun j => subst XR (Φh.toPowerSeries j)
  have hΦL : ∀ j, constantCoeff (ΦL j) = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXL) hXL (hΦc j)
  have hΦR : ∀ j, constantCoeff (ΦR j) = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXR) hXR (hΦc j)
  let sw : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) C := Sum.elim XR XL
  have hsw : HasSubst sw := hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)

  have hG : ∀ i, G''.toPowerSeries i =
      subst (fun j => subst (Sum.elim ΦL ΦR) (F''.toPowerSeries j)) (Ψh.toPowerSeries i) := by
    intro i
    have e1 : subst G''.toPowerSeries (subst Φh.toPowerSeries (Ψh.toPowerSeries i)) =
        G''.toPowerSeries i := by
      have := congrFun h i
      simp only [Series.comp] at this
      rw [this]
      exact subst_X G''.hasSubst_toPowerSeries i
    rw [← e1, subst_comp_subst_apply Φh.hasSubst_toPowerSeries G''.hasSubst_toPowerSeries]
    congr 1
    funext j
    exact Φh.subst_eq j
  constructor
  intro i
  rw [hG i, subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero fun j =>
      MvFormalGroup.constantCoeff_subst_elim F'' hΦL hΦR j) hsw]
  congr 1
  funext j
  show subst sw (subst (Sum.elim ΦL ΦR) (F''.toPowerSeries j)) =
    subst (Sum.elim ΦL ΦR) (F''.toPowerSeries j)
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hΦL hΦR) hsw]
  have hfam : (fun s => subst sw (Sum.elim ΦL ΦR s)) = Sum.elim ΦR ΦL := by
    funext s
    rcases s with j | j
    · show subst sw (subst XL (Φh.toPowerSeries j)) = subst XR (Φh.toPowerSeries j)
      rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hXL) hsw]
      congr 1
      funext l
      exact subst_X hsw (Sum.inl l)
    · show subst sw (subst XR (Φh.toPowerSeries j)) = subst XL (Φh.toPowerSeries j)
      rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hXR) hsw]
      congr 1
      funext l
      exact subst_X hsw (Sum.inr l)
  rw [hfam]
  exact MvFormalGroup.subst_elim_comm F'' hΦR hΦL j

end transport

section square

variable {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
  (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
  (hcomm : q'.comp p' = q''.comp p'')
  (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')

include hcomm hpb in
theorem eq_of_proj_eq {b₁ b₂ : B} (h' : p' b₁ = p' b₂) (h'' : p'' b₁ = p'' b₂) : b₁ = b₂ := by
  have hc : q' (p' b₁) = q'' (p'' b₁) := by
    have := congrArg (fun g => g b₁) hcomm
    simpa using this
  obtain ⟨b, -, huniq⟩ := hpb (p' b₁) (p'' b₁) hc
  exact (huniq b₁ ⟨rfl, rfl⟩).trans (huniq b₂ ⟨h'.symm, h''.symm⟩).symm

include hcomm hpb in
theorem mv_eq_of_proj_eq {τ : Type*} {g₁ g₂ : MvPowerSeries τ B}
    (h' : MvPowerSeries.map p' g₁ = MvPowerSeries.map p' g₂)
    (h'' : MvPowerSeries.map p'' g₁ = MvPowerSeries.map p'' g₂) : g₁ = g₂ := by
  ext n
  apply eq_of_proj_eq p' p'' q' q'' hcomm hpb
  · have := congrArg (MvPowerSeries.coeff n) h'
    simpa only [MvPowerSeries.coeff_map] using this
  · have := congrArg (MvPowerSeries.coeff n) h''
    simpa only [MvPowerSeries.coeff_map] using this

include hcomm hpb in
theorem series_eq_of_proj_eq {s₁ s₂ : Series B} (h' : s₁.map p' = s₂.map p')
    (h'' : s₁.map p'' = s₂.map p'') : s₁ = s₂ := by
  funext i
  exact mv_eq_of_proj_eq p' p'' q' q'' hcomm hpb (congrFun h' i) (congrFun h'' i)

include q' q'' hcomm hpb in

theorem isODHom_of_proj (Y₁ Y₂ : FormalODModule q B) (α : Y₁.F.Hom Y₂.F)
    (v' : (Y₁.map p').Hom (Y₂.map p')) (v'' : (Y₁.map p'').Hom (Y₂.map p''))
    (hα' : Series.map p' α.toPowerSeries = v'.toSeries)
    (hα'' : Series.map p'' α.toPowerSeries = v''.toSeries) :
    IsODHom Y₁ Y₂ α.toPowerSeries := by
  have hαcc : ∀ i, constantCoeff (α.toPowerSeries i) = 0 := α.constantCoeff_eq_zero
  refine ⟨IsLawHom.of_hom α, fun a => ?_, ?_⟩
  · apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
    · rw [Series.map_comp p' _ _ (Y₁.isLawHom_act a).1, hα',
        Series.map_comp p' _ _ hαcc, hα']
      exact v'.isODHom.2.1 a
    · rw [Series.map_comp p'' _ _ (Y₁.isLawHom_act a).1, hα'',
        Series.map_comp p'' _ _ hαcc, hα'']
      exact v''.isODHom.2.1 a
  · apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
    · rw [Series.map_comp p' _ _ Y₁.isLawHom_varpi.1, hα',
        Series.map_comp p' _ _ hαcc, hα']
      exact v'.isODHom.2.2
    · rw [Series.map_comp p'' _ _ Y₁.isLawHom_varpi.1, hα'',
        Series.map_comp p'' _ _ hαcc, hα'']
      exact v''.isODHom.2.2

variable {k : Type u} [Field k] [CharP k q] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
  (resB : B →+* k) (resA' : A' →+* k) (resA'' : A'' →+* k) (resA : A →+* k)
  (hresA' : resA'.comp p' = resB) (hresA'' : resA''.comp p'' = resB)
  (hresq' : resA.comp q' = resA') (hresq'' : resA.comp q'' = resA'')
  (hresA : Function.Surjective resA) (hnil : IsNilpotent (RingHom.ker resA))

theorem eq_inv_comp {C : Type u} [CommRing C] {u₂ g₂ x u₁ : Series C}
    (hu₂ : ∀ i, constantCoeff (u₂ i) = 0) (hx : ∀ i, constantCoeff (x i) = 0)
    (hg : g₂.comp u₂ = Series.id C) (h : u₂.comp x = u₁) : x = g₂.comp u₁ := by
  rw [← h, ← Series.comp_assoc _ _ _ hu₂ hx, hg, Series.id_comp _ hx]

include hcomm hpb hresA' hresq' hresq'' hresA hnil in

theorem glue_iso (Y₁ : FormalODModule q B) (u₁ : (Y₁.map resB).Hom X₀.toFormalODModule)
    (hu₁ : u₁.IsIso) (Y₂ : FormalODModule q B) (u₂ : (Y₂.map resB).Hom X₀.toFormalODModule)
    (hu₂ : u₂.IsIso) (v' : (Y₁.map p').Hom (Y₂.map p')) (hv' : v'.IsIso)
    (hc' : u₂.toSeries.comp (v'.toSeries.map resA') = u₁.toSeries)
    (v'' : (Y₁.map p'').Hom (Y₂.map p'')) (hv'' : v''.IsIso)
    (hc'' : u₂.toSeries.comp (v''.toSeries.map resA'') = u₁.toSeries) :
    ∃ v : Y₁.Hom Y₂, v.IsIso ∧ v.toSeries.map p' = v'.toSeries ∧
      v.toSeries.map p'' = v''.toSeries ∧
      u₂.toSeries.comp (v.toSeries.map resB) = u₁.toSeries := by

  have hresr : resA.comp (q'.comp p') = resB := by
    rw [← RingHom.comp_assoc, hresq', hresA']

  have hs'cc : ∀ i, constantCoeff ((v'.toSeries.map q') i) = 0 := cc_map (hom_cc v') q'
  have hs''cc : ∀ i, constantCoeff ((v''.toSeries.map q'') i) = 0 := cc_map (hom_cc v'') q''
  have hs'k : (v'.toSeries.map q').map resA = v'.toSeries.map resA' := by
    rw [Series.map_map, hresq']
  have hs''k : (v''.toSeries.map q'').map resA = v''.toSeries.map resA'' := by
    rw [Series.map_map, hresq'']

  obtain ⟨g₂, hg₂, -⟩ := hu₂
  have eg₂ := congrArg FormalODModule.Hom.toSeries hg₂
  simp only [comp_toSeries, id_toSeries] at eg₂
  have hred : (v'.toSeries.map q').map resA = (v''.toSeries.map q'').map resA := by
    have hx' : u₂.toSeries.comp ((v'.toSeries.map q').map resA) = u₁.toSeries := by
      rw [hs'k]; exact hc'
    have hx'' : u₂.toSeries.comp ((v''.toSeries.map q'').map resA) = u₁.toSeries := by
      rw [hs''k]; exact hc''
    rw [eq_inv_comp (hom_cc u₂) (cc_map hs'cc resA) eg₂ hx',
      eq_inv_comp (hom_cc u₂) (cc_map hs''cc resA) eg₂ hx'']

  have h1 : IsLawHom (Y₁.map (q'.comp p')).F (Y₂.map (q'.comp p')).F (v'.toSeries.map q') := by
    have h0 : IsLawHom ((Y₁.map p').map q').F ((Y₂.map p').map q').F (v'.toSeries.map q') :=
      (v'.map q').isODHom.1
    rwa [FormalODModule.map_map, FormalODModule.map_map] at h0
  have h2 : IsLawHom (Y₁.map (q'.comp p')).F (Y₂.map (q'.comp p')).F (v''.toSeries.map q'') := by
    have h0 : IsLawHom ((Y₁.map p'').map q'').F ((Y₂.map p'').map q'').F (v''.toSeries.map q'') :=
      (v''.map q'').isODHom.1
    rwa [FormalODModule.map_map, FormalODModule.map_map, ← hcomm] at h0

  have hh : Module.finrank k (MvPowerSeries (Fin 2) k ⧸
      Ideal.span (Set.range (((Y₁.map (q'.comp p')).F.map resA).nthSeries q))) = q ^ 4 := by
    have hF : (Y₁.map (q'.comp p')).F.map resA = (Y₁.map resB).F := by
      rw [← FormalODModule.map_F, FormalODModule.map_map, hresr]
    rw [hF]
    exact finrank_of_iso X₀ (Y₁.map resB) u₁ hu₁
  obtain ⟨n, hn⟩ := hnil
  have hI : RingHom.ker resA ^ (n + 1) = ⊥ := by
    rw [pow_succ, hn, Ideal.zero_eq_bot, Ideal.bot_mul]
  have hs : v'.toSeries.map q' = v''.toSeries.map q'' := by
    have := MvFormalGroup.Hom.eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow resA hresA n hI q
      (Y₁.map (q'.comp p')).F (Y₂.map (q'.comp p')).F 4 hh h1.toHom h2.toHom
      (fun i => congrFun hred i)
    exact congrArg MvFormalGroup.Hom.toPowerSeries this

  obtain ⟨-, part2⟩ :=
    MvFormalGroup.exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective p' p'' q' q'' hcomm hpb 2
  obtain ⟨α, ⟨hα', hα''⟩, -⟩ := part2 Y₁.F Y₂.F v'.toLawHom v''.toLawHom (fun i => congrFun hs i)
  have hα's : Series.map p' α.toPowerSeries = v'.toSeries := funext hα'
  have hα''s : Series.map p'' α.toPowerSeries = v''.toSeries := funext hα''
  let v : Y₁.Hom Y₂ :=
    ⟨α.toPowerSeries, isODHom_of_proj p' p'' q' q'' hcomm hpb Y₁ Y₂ α v' v'' hα's hα''s⟩

  obtain ⟨g', hg'₁, hg'₂⟩ := hv'
  obtain ⟨g'', hg''₁, hg''₂⟩ := hv''
  have eg'₁ := congrArg FormalODModule.Hom.toSeries hg'₁
  have eg'₂ := congrArg FormalODModule.Hom.toSeries hg'₂
  have eg''₁ := congrArg FormalODModule.Hom.toSeries hg''₁
  have eg''₂ := congrArg FormalODModule.Hom.toSeries hg''₂
  simp only [comp_toSeries, id_toSeries] at eg'₁ eg'₂ eg''₁ eg''₂
  have ht : g'.toSeries.map q' = g''.toSeries.map q'' := by
    apply inverse_unique hs'cc (cc_map (hom_cc g'') q'')
    · rw [← Series.map_comp q' _ _ (hom_cc v'), eg'₁, Series.map_id]
    · rw [hs, ← Series.map_comp q'' _ _ (hom_cc g''), eg''₂, Series.map_id]
  obtain ⟨γ, ⟨hγ', hγ''⟩, -⟩ := part2 Y₂.F Y₁.F g'.toLawHom g''.toLawHom (fun i => congrFun ht i)
  have hγ's : Series.map p' γ.toPowerSeries = g'.toSeries := funext hγ'
  have hγ''s : Series.map p'' γ.toPowerSeries = g''.toSeries := funext hγ''
  let w : Y₂.Hom Y₁ :=
    ⟨γ.toPowerSeries, isODHom_of_proj p' p'' q' q'' hcomm hpb Y₂ Y₁ γ g' g'' hγ's hγ''s⟩
  have hvs : v.toSeries = α.toPowerSeries := rfl
  have hws : w.toSeries = γ.toPowerSeries := rfl
  have hvcc : ∀ i, constantCoeff (v.toSeries i) = 0 := hom_cc v
  have hwcc : ∀ i, constantCoeff (w.toSeries i) = 0 := hom_cc w
  have hwv : w.comp v = FormalODModule.Hom.id Y₁ := by
    apply FormalODModule.Hom.ext
    apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
    · rw [comp_toSeries, id_toSeries, Series.map_comp p' _ _ hvcc, Series.map_id, hvs, hws,
        hγ's, hα's, eg'₁]
    · rw [comp_toSeries, id_toSeries, Series.map_comp p'' _ _ hvcc, Series.map_id, hvs, hws,
        hγ''s, hα''s, eg''₁]
  have hvw : v.comp w = FormalODModule.Hom.id Y₂ := by
    apply FormalODModule.Hom.ext
    apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
    · rw [comp_toSeries, id_toSeries, Series.map_comp p' _ _ hwcc, Series.map_id, hvs, hws,
        hγ's, hα's, eg'₂]
    · rw [comp_toSeries, id_toSeries, Series.map_comp p'' _ _ hwcc, Series.map_id, hvs, hws,
        hγ''s, hα''s, eg''₂]
  refine ⟨v, ⟨w, hwv, hvw⟩, hα's, hα''s, ?_⟩
  have hfin : Series.map resB α.toPowerSeries = v'.toSeries.map resA' := by
    rw [← hα's, Series.map_map, hresA']
  rw [hvs, hfin]
  exact hc'

include hcomm hpb hresA' hresq'' in

theorem glue_obj (hq'' : Function.Surjective q'') (hq''loc : IsLocalHom q'')
    (X' : FormalODModule q A') (w' : (X'.map resA').Hom X₀.toFormalODModule) (hw' : w'.IsIso)
    (X'' : FormalODModule q A'') (w'' : (X''.map resA'').Hom X₀.toFormalODModule)
    (φ : (X'.map q').Hom (X''.map q'')) (hφ : φ.IsIso)
    (hcφ : w''.toSeries.comp (φ.toSeries.map resA) = w'.toSeries) :
    ∃ (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule), u.IsIso ∧
      Y.map p' = X' ∧ u.toSeries = w'.toSeries ∧
      ∃ v : (Y.map p'').Hom X'', v.IsIso ∧ v.toSeries.map q'' = φ.toSeries ∧
        w''.toSeries.comp (v.toSeries.map resA'') = u.toSeries := by
  classical

  have hunit : IsUnit (MvFormalGroup.linearPart φ.toLawHom.toPowerSeries) := by
    obtain ⟨ψ, hψ₁, hψ₂⟩ := hφ
    have e1 := congrArg FormalODModule.Hom.toSeries hψ₁
    have e2 := congrArg FormalODModule.Hom.toSeries hψ₂
    simp only [comp_toSeries, id_toSeries] at e1 e2
    have l1 := MvFormalGroup.linearPart_subst (hom_cc φ) ψ.toSeries
    have l2 := MvFormalGroup.linearPart_subst (hom_cc ψ) φ.toSeries
    change MvFormalGroup.linearPart (ψ.toSeries.comp φ.toSeries) = _ at l1
    change MvFormalGroup.linearPart (φ.toSeries.comp ψ.toSeries) = _ at l2
    rw [e1] at l1
    rw [e2] at l2
    change MvFormalGroup.linearPart (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) A)) = _
      at l1 l2
    rw [MvFormalGroup.linearPart_X] at l1 l2
    exact ⟨⟨_, _, l2.symm, l1.symm⟩, rfl⟩
  obtain ⟨part1, part2⟩ :=
    MvFormalGroup.exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective p' p'' q' q'' hcomm hpb 2
  obtain ⟨G, Φ, Ψ, hGp', hΨΦ, hΦΨ, hΦφ⟩ := part1 hq'' hq''loc X'.F X''.F φ.toLawHom hunit
  have hΦc : ∀ i, constantCoeff (Φ.toPowerSeries i) = 0 := Φ.constantCoeff_eq_zero
  have hΨc : ∀ i, constantCoeff (Ψ.toPowerSeries i) = 0 := Ψ.constantCoeff_eq_zero
  have eΨΦ : Series.comp Ψ.toPowerSeries Φ.toPowerSeries = Series.id A'' :=
    congrArg MvFormalGroup.Hom.toPowerSeries hΨΦ
  have eΦΨ : Series.comp Φ.toPowerSeries Ψ.toPowerSeries = Series.id A'' :=
    congrArg MvFormalGroup.Hom.toPowerSeries hΦΨ
  have hΦφs : Series.map q'' Φ.toPowerSeries = φ.toSeries := funext hΦφ

  have hex : ∀ (e' : Series A') (e'' : Series A''), IsLawHom X'.F X'.F e' →
      IsLawHom X''.F X''.F e'' → φ.toSeries.comp (e'.map q') = (e''.map q'').comp φ.toSeries →
      ∃ α : Series B, IsLawHom G G α ∧ α.map p' = e' ∧
        α.map p'' = trans Φ.toPowerSeries Ψ.toPowerSeries e'' := by
    intro e' e'' he' he'' hce
    have he'G : IsLawHom (G.map p') (G.map p') e' := by rw [hGp']; exact he'
    have he''G : IsLawHom (G.map p'') (G.map p'') (trans Φ.toPowerSeries Ψ.toPowerSeries e'') :=
      isLawHom_trans Φ Ψ he''
    have hagree : ∀ i, MvPowerSeries.map q' (he'G.toHom.toPowerSeries i) =
        MvPowerSeries.map q'' (he''G.toHom.toPowerSeries i) := by
      intro i
      simp only [IsLawHom.toHom_toPowerSeries]
      have hψφ : (Series.map q'' Ψ.toPowerSeries).comp φ.toSeries = Series.id A := by
        rw [← hΦφs, ← Series.map_comp q'' _ _ hΦc, eΨΦ, Series.map_id]
      have key : (trans Φ.toPowerSeries Ψ.toPowerSeries e'').map q'' = e'.map q' := by
        rw [map_trans q'' he''.1 hΦc, trans, hΦφs, ← hce,
          ← Series.comp_assoc _ _ _ (hom_cc φ) (cc_map he'.1 q'), hψφ,
          Series.id_comp _ (cc_map he'.1 q')]
      exact (congrFun key i).symm
    obtain ⟨α, ⟨hα', hα''⟩, -⟩ := part2 G G he'G.toHom he''G.toHom hagree
    exact ⟨α.toPowerSeries, IsLawHom.of_hom α, funext hα', funext hα''⟩
  choose glue hglue_law hglue' hglue'' using hex

  have hφact : ∀ a, φ.toSeries.comp ((X'.act a).map q') = ((X''.act a).map q'').comp φ.toSeries :=
    fun a => φ.isODHom.2.1 a
  have hφvarpi : φ.toSeries.comp (X'.varpi.map q') = (X''.varpi.map q'').comp φ.toSeries :=
    φ.isODHom.2.2

  let actB : Zp2 q → Series B := fun a =>
    glue (X'.act a) (X''.act a) (X'.isLawHom_act a) (X''.isLawHom_act a) (hφact a)
  let varpiB : Series B :=
    glue X'.varpi X''.varpi X'.isLawHom_varpi X''.isLawHom_varpi hφvarpi
  have hact' : ∀ a, (actB a).map p' = X'.act a := fun a => hglue' _ _ _ _ _
  have hact'' : ∀ a, (actB a).map p'' = trans Φ.toPowerSeries Ψ.toPowerSeries (X''.act a) :=
    fun a => hglue'' _ _ _ _ _
  have hvarpi' : varpiB.map p' = X'.varpi := hglue' _ _ _ _ _
  have hvarpi'' : varpiB.map p'' = trans Φ.toPowerSeries Ψ.toPowerSeries X''.varpi :=
    hglue'' _ _ _ _ _
  have hactcc : ∀ a i, constantCoeff (actB a i) = 0 := fun a => (hglue_law _ _ _ _ _).1
  have hvarpicc : ∀ i, constantCoeff (varpiB i) = 0 := (hglue_law _ _ _ _ _).1
  have hact''cc : ∀ a i, constantCoeff (X''.act a i) = 0 := fun a => (X''.isLawHom_act a).1
  have hvarpi''cc : ∀ i, constantCoeff (X''.varpi i) = 0 := X''.isLawHom_varpi.1

  have hGcomm : G.IsComm := by
    haveI : (G.map p'').IsComm := isComm_of_hom Φ Ψ eΨΦ
    haveI : (G.map p').IsComm := by rw [hGp']; exact X'.isComm
    constructor
    intro i
    apply mv_eq_of_proj_eq p' p'' q' q'' hcomm hpb
    · have := MvFormalGroup.IsComm.comm (F := G.map p') i
      have hsw : HasSubst (Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          fun j => MvPowerSeries.X (Sum.inl j)) :=
        hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
      rw [map_subst hsw]
      have hfam : (fun s => MvPowerSeries.map p' (Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          (fun j => MvPowerSeries.X (Sum.inl j)) s)) = Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) A'))
          fun j => MvPowerSeries.X (Sum.inl j) := by
        funext s; rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
      rw [hfam]
      exact this
    · have := MvFormalGroup.IsComm.comm (F := G.map p'') i
      have hsw : HasSubst (Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          fun j => MvPowerSeries.X (Sum.inl j)) :=
        hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
      rw [map_subst hsw]
      have hfam : (fun s => MvPowerSeries.map p'' (Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          (fun j => MvPowerSeries.X (Sum.inl j)) s)) = Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) A''))
          fun j => MvPowerSeries.X (Sum.inl j) := by
        funext s; rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
      rw [hfam]
      exact this

  let Y : FormalODModule q B :=
    { F := G
      isComm := hGcomm
      act := actB
      varpi := varpiB
      isLawHom_act := fun a => hglue_law _ _ _ _ _
      isLawHom_varpi := hglue_law _ _ _ _ _
      act_one := by
        apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [hact', X'.act_one, Series.map_id]
        · rw [hact'', X''.act_one, trans_id hΦc eΨΦ, Series.map_id]
      act_mul := fun a b => by
        apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [hact', X'.act_mul, Series.map_comp p' _ _ (hactcc b), hact', hact']
        · rw [hact'', X''.act_mul, trans_comp hΦc hΨc eΦΨ (hact''cc a) (hact''cc b),
            Series.map_comp p'' _ _ (hactcc b), hact'', hact'']
      act_add := fun a b => by
        apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [hact', X'.act_add, Series.map_addVia p' G _ _ (hactcc a) (hactcc b), hact', hact', hGp']
        · rw [hact'', X''.act_add, Series.map_addVia p'' G _ _ (hactcc a) (hactcc b), hact'', hact'',
            trans_addVia Φ Ψ (hact''cc a) (hact''cc b)]
      varpi_comp_varpi := by
        apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [Series.map_comp p' _ _ hvarpicc, hvarpi', X'.varpi_comp_varpi, hact']
        · rw [Series.map_comp p'' _ _ hvarpicc, hvarpi'', hact'',
            ← trans_comp hΦc hΨc eΦΨ hvarpi''cc hvarpi''cc, X''.varpi_comp_varpi]
      varpi_comp_act := fun a => by
        apply series_eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [Series.map_comp p' _ _ (hactcc a), hvarpi', hact', X'.varpi_comp_act,
            Series.map_comp p' _ _ hvarpicc, hvarpi', hact']
        · rw [Series.map_comp p'' _ _ (hactcc a), hvarpi'', hact'',
            ← trans_comp hΦc hΨc eΦΨ hvarpi''cc (hact''cc a), X''.varpi_comp_act,
            trans_comp hΦc hΨc eΦΨ (hact''cc _) hvarpi''cc,
            Series.map_comp p'' _ _ hvarpicc, hvarpi'', hact''] }

  have hYp' : Y.map p' = X' :=
    FormalODModule.ext' hGp' (funext fun a => hact' a) hvarpi'
  have hYres : X'.map resA' = Y.map resB := by
    rw [← hYp', FormalODModule.map_map, hresA']

  have hvOD : IsODHom (Y.map p'') X'' Φ.toPowerSeries := by
    refine ⟨IsLawHom.of_hom Φ, fun a => ?_, ?_⟩
    · show Series.comp Φ.toPowerSeries ((actB a).map p'') = (X''.act a).comp Φ.toPowerSeries
      rw [hact'', comp_trans hΦc hΨc eΦΨ (hact''cc a)]
    · show Series.comp Φ.toPowerSeries (varpiB.map p'') = X''.varpi.comp Φ.toPowerSeries
      rw [hvarpi'', comp_trans hΦc hΨc eΦΨ hvarpi''cc]
  have hwOD : IsODHom X'' (Y.map p'') Ψ.toPowerSeries := by
    refine ⟨IsLawHom.of_hom Ψ, fun a => ?_, ?_⟩
    · show Series.comp Ψ.toPowerSeries (X''.act a) = ((actB a).map p'').comp Ψ.toPowerSeries
      rw [hact'', trans_comp_inv hΦc hΨc eΦΨ (hact''cc a)]
    · show Series.comp Ψ.toPowerSeries X''.varpi = (varpiB.map p'').comp Ψ.toPowerSeries
      rw [hvarpi'', trans_comp_inv hΦc hΨc eΦΨ hvarpi''cc]
  let v : (Y.map p'').Hom X'' := ⟨Φ.toPowerSeries, hvOD⟩
  let vinv : X''.Hom (Y.map p'') := ⟨Ψ.toPowerSeries, hwOD⟩
  have hviso : v.IsIso :=
    ⟨vinv, FormalODModule.Hom.ext eΨΦ, FormalODModule.Hom.ext eΦΨ⟩
  refine ⟨Y, castHom hYres w', castHom_isIso hYres w' hw', hYp', rfl, v, hviso, hΦφs, ?_⟩
  show w''.toSeries.comp (Series.map resA'' Φ.toPowerSeries) = w'.toSeries
  have hfin : Series.map resA'' Φ.toPowerSeries = φ.toSeries.map resA := by
    rw [← hΦφs, Series.map_map, hresq'']
  rw [hfin]
  exact hcφ

end square

end R4ODGlue
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal R4ODGlue in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : CerednikDrinfeld.Zp2 q →+* k} (X₀ : CerednikDrinfeld.SpecialFormalODModule q j₀)
    {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
    (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
    (hcomm : q'.comp p' = q''.comp p'')
    (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')
    (hq'' : Function.Surjective q'') (hq''loc : IsLocalHom q'')
    (resB : B →+* k) (resA' : A' →+* k) (resA'' : A'' →+* k) (resA : A →+* k)
    (hresA' : resA'.comp p' = resB) (hresA'' : resA''.comp p'' = resB)
    (hresq' : resA.comp q' = resA') (hresq'' : resA.comp q'' = resA'')
    (hresA : Function.Surjective resA) (hnil : IsNilpotent (RingHom.ker resA)) :
    (∀ (X' : CerednikDrinfeld.FormalODModule q A')
        (w' : (X'.map resA').Hom X₀.toFormalODModule), w'.IsIso →
      ∀ (X'' : CerednikDrinfeld.FormalODModule q A'')
        (w'' : (X''.map resA'').Hom X₀.toFormalODModule), w''.IsIso →
      ∀ (φ : (X'.map q').Hom (X''.map q'')), φ.IsIso →
        w''.toSeries.comp (φ.toSeries.map resA) = w'.toSeries →
        ∃ (Y : CerednikDrinfeld.FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule),
          u.IsIso ∧ Y.map p' = X' ∧ u.toSeries = w'.toSeries ∧
          ∃ v : (Y.map p'').Hom X'', v.IsIso ∧ v.toSeries.map q'' = φ.toSeries ∧
            w''.toSeries.comp (v.toSeries.map resA'') = u.toSeries) ∧
    (∀ (Y₁ : CerednikDrinfeld.FormalODModule q B) (u₁ : (Y₁.map resB).Hom X₀.toFormalODModule),
        u₁.IsIso →
      ∀ (Y₂ : CerednikDrinfeld.FormalODModule q B) (u₂ : (Y₂.map resB).Hom X₀.toFormalODModule),
        u₂.IsIso →
      ∀ (v' : (Y₁.map p').Hom (Y₂.map p')), v'.IsIso →
        u₂.toSeries.comp (v'.toSeries.map resA') = u₁.toSeries →
      ∀ (v'' : (Y₁.map p'').Hom (Y₂.map p'')), v''.IsIso →
        u₂.toSeries.comp (v''.toSeries.map resA'') = u₁.toSeries →
        ∃ v : Y₁.Hom Y₂, v.IsIso ∧ v.toSeries.map p' = v'.toSeries ∧
          v.toSeries.map p'' = v''.toSeries ∧
          u₂.toSeries.comp (v.toSeries.map resB) = u₁.toSeries) := by
  refine ⟨fun X' w' hw' X'' w'' _ φ hφ hcφ => ?_, fun Y₁ u₁ hu₁ Y₂ u₂ hu₂ v' hv' hc' v'' hv'' hc'' => ?_⟩
  · exact glue_obj p' p'' q' q'' hcomm hpb X₀ resB resA' resA'' resA hresA' hresq'' hq'' hq''loc
      X' w' hw' X'' w'' φ hφ hcφ
  · exact glue_iso p' p'' q' q'' hcomm hpb X₀ resB resA' resA'' resA hresA' hresq' hresq'' hresA hnil
      Y₁ u₁ hu₁ Y₂ u₂ hu₂ v' hv' hc' v'' hv'' hc''

end S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective (solution)
