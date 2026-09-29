-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_forall_isIsomorphic_map_localizationAway
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/54f3b4ad-98d0-50a1-b918-a0d15da9ee7a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_forall_isIsomorphic_map_localizationAway

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

noncomputable section

open scoped Classical

namespace DescGlue

p2m_open "MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule"

variable {p : ℕ} [Fact p.Prime]

section inj
variable {B : Type u} [CommRing B] {ι' : Type*} {C : ι' → Type u} [∀ a, CommRing (C a)]
  (g : ∀ a, B →+* C a)

def JointlyInjective : Prop := ∀ x y : B, (∀ a, g a x = g a y) → x = y

variable {g}

theorem JointlyInjective.mvPowerSeries_eq {σ : Type*} (hg : JointlyInjective g) {F G : MvPowerSeries σ B}
    (h : ∀ a, MvPowerSeries.map (g a) F = MvPowerSeries.map (g a) G) : F = G := by
  ext d
  exact hg _ _ (fun a => by simpa only [coeff_map] using congrArg (coeff d) (h a))

theorem JointlyInjective.series_eq (hg : JointlyInjective g) {φ ψ : Series B}
    (h : ∀ a, φ.map (g a) = ψ.map (g a)) : φ = ψ :=
  funext fun i => hg.mvPowerSeries_eq (fun a => congrFun (h a) i)

end inj

section lawmap
variable {B B' : Type u} [CommRing B] [CommRing B']

theorem map_law_lhs (f : B →+* B') (F : MvFormalGroup 2 B) (φ : Series B) (i : Fin 2) :
    MvPowerSeries.map f (subst F.toPowerSeries (φ i)) = subst (F.map f).toPowerSeries ((φ.map f) i) := by
  rw [map_subst F.hasSubst_toPowerSeries]
  rfl

theorem map_law_rhs (f : B →+* B') (G : MvFormalGroup 2 B) (φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (i : Fin 2) :
    MvPowerSeries.map f (subst
      (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
      (G.toPowerSeries i)) =
    subst
      (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B')) ((φ.map f) j))
        fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B')) ((φ.map f) j))
      ((G.map f).toPowerSeries i) := by
  have hXl : ∀ l : Fin 2, constantCoeff
      ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 :=
    fun l => constantCoeff_X _
  have hXr : ∀ l : Fin 2, constantCoeff
      ((MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 :=
    fun l => constantCoeff_X _
  have hA : HasSubst (Sum.elim
      (fun j => subst
        (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
      fun j => subst
        (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXl) hXl (hφ j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXr) hXr (hφ j)
  rw [map_subst hA]
  have hAmap : (fun s => MvPowerSeries.map f (Sum.elim
      (fun j => subst
        (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
      (fun j => subst
        (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j)) s))
      = Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
            (MvPowerSeries.map f (φ j)))
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
            (MvPowerSeries.map f (φ j))) := by
    funext s
    rcases s with j | j
    · show MvPowerSeries.map f (subst _ (φ j)) = _
      rw [map_subst (hasSubst_of_constantCoeff_zero hXl)]
      simp only [MvPowerSeries.map_X, Sum.elim_inl]
    · show MvPowerSeries.map f (subst _ (φ j)) = _
      rw [map_subst (hasSubst_of_constantCoeff_zero hXr)]
      simp only [MvPowerSeries.map_X, Sum.elim_inr]
  rw [hAmap]
  rfl

end lawmap

section descend
variable {B : Type u} [CommRing B] {ι' : Type*} {C : ι' → Type u} [∀ a, CommRing (C a)]
  {g : ∀ a, B →+* C a}

theorem isLawHom_of_forall_map (hg : JointlyInjective g) (F G : MvFormalGroup 2 B) (φ : Series B)
    (h : ∀ a, IsLawHom (F.map (g a)) (G.map (g a)) (φ.map (g a))) :
    IsLawHom F G φ := by
  have hφ : ∀ i, constantCoeff (φ i) = 0 := by
    intro i
    apply hg
    intro a
    have := (h a).1 i
    rw [map_zero]
    rwa [Series.map, constantCoeff_map] at this
  refine ⟨hφ, fun i => ?_⟩
  apply hg.mvPowerSeries_eq
  intro a
  rw [map_law_lhs, map_law_rhs _ _ _ hφ]
  exact (h a).2 i

theorem isODHom_of_forall_map (hg : JointlyInjective g) (X Y : FormalODModule p B) (φ : Series B)
    (h : ∀ a, IsODHom (X.map (g a)) (Y.map (g a)) (φ.map (g a))) : IsODHom X Y φ := by
  have hlaw : IsLawHom X.F Y.F φ := isLawHom_of_forall_map hg X.F Y.F φ (fun a => (h a).1)
  have hφ := hlaw.1
  refine ⟨hlaw, fun a' => ?_, ?_⟩
  · apply hg.series_eq
    intro a
    rw [Series.map_comp _ _ _ (X.isLawHom_act a').1, Series.map_comp _ _ _ hφ]
    exact (h a).2.1 a'
  · apply hg.series_eq
    intro a
    rw [Series.map_comp _ _ _ X.isLawHom_varpi.1, Series.map_comp _ _ _ hφ]
    exact (h a).2.2

end descend

end DescGlue

namespace DescGlue

p2m_open "MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule"

variable {p : ℕ} [Fact p.Prime]

section witness
variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B B' : Type u} [CommRing B] [CommRing B']

def IsIsoWitness (t t' : Rigidified p Φ B) (u v : Series B) (m : ℕ) : Prop :=
  FormalODModule.IsODHom t.X t'.X u ∧ FormalODModule.IsODHom t'.X t.X v ∧
    v.comp u = Series.id B ∧ u.comp v = Series.id B ∧
    (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ)
      = (t'.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp t'.ρ

theorem isIsomorphic_iff (t t' : Rigidified p Φ B) :
    t.IsIsomorphic t' ↔ ∃ u v m, IsIsoWitness t t' u v m := Iff.rfl

omit [Fact p.Prime] in
theorem reduceMap_comp_mk (f : B →+* B') :
    (reduceMap (p := p) f).comp (Ideal.Quotient.mk (pIdeal p B)) = (Ideal.Quotient.mk (pIdeal p B')).comp f :=
  RingHom.ext fun x => rfl

theorem Xbar_map (f : B →+* B') (t : Rigidified p Φ B) :
    (t.map f).Xbar = t.Xbar.map (reduceMap f) := by
  show (t.X.map f).map (Ideal.Quotient.mk (pIdeal p B')) = (t.X.map _).map _
  rw [FormalODModule.map_map, FormalODModule.map_map, reduceMap_comp_mk]

theorem act_pow_zero' {C : Type u} [CommRing C] (Y : FormalODModule p C) (a : ℕ) (i : Fin 2) :
    MvPowerSeries.constantCoeff (Y.act ((p : Zp2 p) ^ a) i) = 0 := (Y.isLawHom_act _).1 i

theorem compat_pad (t t' : Rigidified p Φ B) (hρ : ∀ i, constantCoeff (t.ρ i) = 0)
    (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0) (u : Series B) (hu : FormalODModule.IsODHom t.X t'.X u)
    (m k : ℕ)
    (h : (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ)
      = (t'.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp t'.ρ) :
    (t'.Xbar.act ((p : Zp2 p) ^ (k + m + t'.n))).comp ((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ)
      = (t'.Xbar.act ((p : Zp2 p) ^ (k + m + t.n))).comp t'.ρ := by
  have hūρ : ∀ i, constantCoeff (((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) i) = 0 :=
    Series.constantCoeff_comp (hu.map _).constantCoeff hρ
  have := congrArg (fun s => (t'.Xbar.act ((p : Zp2 p) ^ k)).comp s) h
  rw [← Series.comp_assoc _ _ _ (act_pow_zero' _ _) hūρ, ← t'.Xbar.act_mul, ← pow_add, ← add_assoc,
    ← Series.comp_assoc _ _ _ (act_pow_zero' _ _) hρ', ← t'.Xbar.act_mul, ← pow_add, ← add_assoc] at this
  exact this

theorem IsIsoWitness.map {t t' : Rigidified p Φ B} (hρ : ∀ i, constantCoeff (t.ρ i) = 0)
    (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0)
    {u v : Series B} {m : ℕ} (h : IsIsoWitness t t' u v m) (f : B →+* B') :
    IsIsoWitness (t.map f) (t'.map f) (u.map f) (v.map f) m := by
  obtain ⟨hu, hv, hvu, huv, hc⟩ := h
  refine ⟨hu.map f, hv.map f, ?_, ?_, ?_⟩
  · rw [← Series.map_comp f _ _ hu.constantCoeff, hvu, Series.map_id]
  · rw [← Series.map_comp f _ _ hv.constantCoeff, huv, Series.map_id]
  ·
    set mk := Ideal.Quotient.mk (pIdeal p B)
    set mk' := Ideal.Quotient.mk (pIdeal p B')
    set rf := reduceMap (p := p) f
    have hūρ : ∀ i, constantCoeff (((u.map mk).comp t.ρ) i) = 0 :=
      Series.constantCoeff_comp (hu.map _).constantCoeff hρ
    have key := congrArg (Series.map rf) hc
    rw [Series.map_comp rf _ _ hūρ, Series.map_comp rf _ _ hρ, Series.map_comp rf _ _ hρ',
      Series.map_map, reduceMap_comp_mk, ← Series.map_map] at key
    rw [Rigidified.map_n, Rigidified.map_n, Rigidified.map_ρ, Rigidified.map_ρ, Xbar_map]
    exact key

namespace IsIsomorphic
private theorem _root_.DescGlue.IsIsomorphic.map {t t' : Rigidified p Φ B} (hρ : ∀ i, constantCoeff (t.ρ i) = 0)
    (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0)
    (h : t.IsIsomorphic t') (f : B →+* B') : (t.map f).IsIsomorphic (t'.map f) := by
  rw [isIsomorphic_iff] at h ⊢
  obtain ⟨u, v, m, h⟩ := h
  exact ⟨_, _, _, h.map hρ hρ' f⟩

end IsIsomorphic
p2m_export "DescGlue" "IsIsomorphic.map"
end witness

end DescGlue

namespace DescGlue

p2m_open "MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule"

variable {p : ℕ} [Fact p.Prime]

section clause
variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B B' : Type u} [CommRing B] [CommRing B']

theorem map_clause_lhs (t t' : Rigidified p Φ B) (hρ : ∀ i, constantCoeff (t.ρ i) = 0)
    (u : Series B) (hu : ∀ i, constantCoeff (u i) = 0) (e : ℕ) (f : B →+* B') :
    ((t'.Xbar.act ((p : Zp2 p) ^ e)).comp ((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ)).map
        (reduceMap f) =
      ((t'.map f).Xbar.act ((p : Zp2 p) ^ e)).comp
        (((u.map f).map (Ideal.Quotient.mk (pIdeal p B'))).comp (t.map f).ρ) := by
  have hu' : ∀ i, constantCoeff ((u.map (Ideal.Quotient.mk (pIdeal p B))) i) = 0 := by
    intro i; show constantCoeff (MvPowerSeries.map _ (u i)) = 0; rw [constantCoeff_map, hu, map_zero]
  have hūρ : ∀ i, constantCoeff (((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) i) = 0 :=
    Series.constantCoeff_comp hu' hρ
  rw [Series.map_comp _ _ _ hūρ, Series.map_comp _ _ _ hρ, Series.map_map, reduceMap_comp_mk,
    ← Series.map_map, Rigidified.map_ρ, Xbar_map]
  rfl

theorem map_clause_rhs (t' : Rigidified p Φ B) (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0) (e : ℕ)
    (f : B →+* B') :
    ((t'.Xbar.act ((p : Zp2 p) ^ e)).comp t'.ρ).map (reduceMap f) =
      ((t'.map f).Xbar.act ((p : Zp2 p) ^ e)).comp (t'.map f).ρ := by
  rw [Series.map_comp _ _ _ hρ', Rigidified.map_ρ, Xbar_map]
  rfl

theorem constantCoeff_map_eq_zero {φ : Series B} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : B →+* B')
    (i : Fin 2) : constantCoeff ((φ.map f) i) = 0 := by
  show constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [constantCoeff_map, hφ, map_zero]

end clause

section loc
variable {B : Type u} [CommRing B] (s : Set B)

abbrev Ov (a b : ↥s) : Type u := Localization.Away (a.1 * b.1)

noncomputable abbrev ra (a b : ↥s) : Localization.Away a.1 →+* Ov s a b :=
  IsLocalization.Away.awayToAwayRight (P := Ov s a b) a.1 b.1

noncomputable abbrev lb (a b : ↥s) : Localization.Away b.1 →+* Ov s a b :=
  IsLocalization.Away.awayToAwayLeft (P := Ov s a b) b.1 a.1

theorem ra_comp (a b : ↥s) : (ra s a b).comp (algebraMap B (Localization.Away a.1)) = algebraMap B (Ov s a b) :=
  RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a.1) a.1 b.1 x

theorem lb_comp (a b : ↥s) : (lb s a b).comp (algebraMap B (Localization.Away b.1)) = algebraMap B (Ov s a b) :=
  RingHom.ext fun x => IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away b.1) b.1 a.1 x

theorem jointlyInjective_algebraMap (hs : Ideal.span s = ⊤) :
    JointlyInjective (fun a : ↥s => algebraMap B (Localization.Away a.1)) := by
  intro x y h
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  funext a
  exact h a

variable {s}

omit [Fact p.Prime] in
theorem mem_pIdeal_of_forall (hs : Ideal.span s = ⊤) (b : B)
    (h : ∀ a : ↥s, algebraMap B (Localization.Away a.1) b ∈ pIdeal p (Localization.Away a.1)) :
    b ∈ pIdeal p B := by
  let J : Ideal B := Submodule.comap (LinearMap.mulRight B b) (pIdeal p B)
  have hJ : ∀ x, x ∈ J ↔ x * b ∈ pIdeal p B := fun x => Iff.rfl
  have key : ∀ a : ↥s, ∃ N : ℕ, (a.1) ^ N ∈ J := by
    intro a
    have hmap : pIdeal p (Localization.Away a.1) = (pIdeal p B).map (algebraMap B (Localization.Away a.1)) := by
      rw [pIdeal, pIdeal, Ideal.map_span, Set.image_singleton, map_natCast]
    have hb := h a
    rw [hmap, IsLocalization.mem_map_algebraMap_iff (Submonoid.powers a.1)] at hb
    obtain ⟨⟨⟨c, hc⟩, ⟨_, ⟨k, rfl⟩⟩⟩, hck⟩ := hb

    have e1 : algebraMap B (Localization.Away a.1) (b * a.1 ^ k) = algebraMap B _ c := by
      rw [map_mul]; exact hck
    obtain ⟨⟨_, ⟨k', rfl⟩⟩, hk'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a.1) _).mp e1

    refine ⟨k' + k, ?_⟩
    rw [hJ]
    have e2 : a.1 ^ (k' + k) * b = a.1 ^ k' * c := by
      have := hk'
      simp only [] at this
      calc a.1 ^ (k' + k) * b = a.1 ^ k' * (b * a.1 ^ k) := by ring
        _ = a.1 ^ k' * c := this
    rw [e2]
    exact Ideal.mul_mem_left _ _ hc
  have hrad : Ideal.span s ≤ J.radical := by
    rw [Ideal.span_le]
    intro a ha
    obtain ⟨N, hN⟩ := key ⟨a, ha⟩
    exact ⟨N, hN⟩
  rw [hs, top_le_iff, Ideal.radical_eq_top] at hrad
  have : (1 : B) ∈ J := hrad ▸ Submodule.mem_top
  rw [hJ, one_mul] at this
  exact this

theorem jointlyInjective_reduceMap (hs : Ideal.span s = ⊤) :
    JointlyInjective (fun a : ↥s => reduceMap (p := p) (algebraMap B (Localization.Away a.1))) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq]
  apply mem_pIdeal_of_forall hs
  intro a
  have := h a
  change Ideal.Quotient.mk _ (algebraMap B (Localization.Away a.1) x) =
    Ideal.Quotient.mk _ (algebraMap B (Localization.Away a.1) y) at this
  rw [Ideal.Quotient.eq, ← map_sub] at this
  exact this

end loc

section main
variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B : Type u} [CommRing B]

theorem glue_series {s : Set B} (hs : Ideal.span s = ⊤) (W : ∀ a : ↥s, Series (Localization.Away a.1))
    (hW : ∀ a b : ↥s, (W a).map (ra s a b) = (W b).map (lb s a b)) :
    ∃ w : Series B, ∀ a, w.map (algebraMap B (Localization.Away a.1)) = W a := by
  have : ∀ (k : Fin 2) (d : Fin 2 →₀ ℕ), ∃ c : B, ∀ a : ↥s, algebraMap B (Localization.Away a.1) c = coeff d (W a k) := by
    intro k d
    obtain ⟨c, hc, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
      (fun a => coeff d (W a k)) (fun a b => by
        have := congrArg (fun φ : Series (Ov s a b) => coeff d (φ k)) (hW a b)
        change coeff d (MvPowerSeries.map _ (W a k)) = coeff d (MvPowerSeries.map _ (W b k)) at this
        rwa [coeff_map, coeff_map] at this)
    exact ⟨c, hc⟩
  choose c hc using this
  refine ⟨fun k => fun d => c k d, fun a => funext fun k => ?_⟩
  ext d
  show coeff d (MvPowerSeries.map _ _) = _
  rw [coeff_map]
  exact hc k d a

theorem desc [IsNoetherianRing B] (ι : Zp2 p →+* O) (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (hloc : ∀ i, (t.map (algebraMap B (Localization.Away (f i)))).IsIsomorphic
      (t'.map (algebraMap B (Localization.Away (f i)))))
    (admBC : ∀ (B₁ : Type u) [CommRing B₁] (g : B →+* B₁), IsNilpotent (p : B₁) →
      (t.map g).IsAdmissible ι (g.comp ψ)) :
    t.IsIsomorphic t' := by
  set s : Set B := Set.range f with hsdef
  have hρ : ∀ i, constantCoeff (t.ρ i) = 0 := ht.constantCoeff_ρ
  have hρ' : ∀ i, constantCoeff (t'.ρ i) = 0 := ht'.constantCoeff_ρ

  have hloc' : ∀ a : ↥s, ∃ u v m, IsIsoWitness (t.map (algebraMap B (Localization.Away a.1)))
      (t'.map (algebraMap B (Localization.Away a.1))) u v m := by
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact (isIsomorphic_iff _ _).mp (hloc i)
  choose U V M hW using hloc'

  have hρa : ∀ a : ↥s, ∀ i, constantCoeff ((t.map (algebraMap B (Localization.Away a.1))).ρ i) = 0 :=
    fun a => constantCoeff_map_eq_zero hρ _
  have hρa' : ∀ a : ↥s, ∀ i, constantCoeff ((t'.map (algebraMap B (Localization.Away a.1))).ρ i) = 0 :=
    fun a => constantCoeff_map_eq_zero hρ' _

  have agreeU : ∀ a b : ↥s, (U a).map (ra s a b) = (U b).map (lb s a b) := by
    intro a b
    have hWa := (hW a).map (hρa a) (hρa' a) (ra s a b)
    have hWb := (hW b).map (hρa b) (hρa' b) (lb s a b)
    rw [← Rigidified.map_comp, ← Rigidified.map_comp, ra_comp] at hWa
    rw [← Rigidified.map_comp, ← Rigidified.map_comp, lb_comp] at hWb
    obtain ⟨hu₁, -, -, -, hc₁⟩ := hWa
    obtain ⟨hu₂, -, -, -, hc₂⟩ := hWb
    have hP : IsNilpotent ((p : ℕ) : Ov s a b) := by
      obtain ⟨k, hk⟩ := hB; exact ⟨k, by rw [← map_natCast (algebraMap B (Ov s a b)), ← map_pow, hk, map_zero]⟩
    exact CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isODHom_of_act_pow_comp_map_comp_eq hP ι
      ((algebraMap B (Ov s a b)).comp ψ) _ _ (admBC _ _ hP) (constantCoeff_map_eq_zero hρ' _)
      _ _ (M a) (M b) hu₁ hu₂ hc₁ hc₂
  have agreeV : ∀ a b : ↥s, (V a).map (ra s a b) = (V b).map (lb s a b) := by
    intro a b
    obtain ⟨hua, hva, hvua, huva, -⟩ := hW a
    obtain ⟨hub, hvb, hvub, huvb, -⟩ := hW b
    have h1 : ((V a).map (ra s a b)).comp ((U a).map (ra s a b)) = Series.id _ := by
      rw [← Series.map_comp _ _ _ hua.constantCoeff, hvua, Series.map_id]
    have h2 : ((U b).map (lb s a b)).comp ((V b).map (lb s a b)) = Series.id _ := by
      rw [← Series.map_comp _ _ _ hvb.constantCoeff, huvb, Series.map_id]
    calc (V a).map (ra s a b) = ((V a).map (ra s a b)).comp (Series.id _) := (Series.comp_id _).symm
      _ = ((V a).map (ra s a b)).comp (((U b).map (lb s a b)).comp ((V b).map (lb s a b))) := by rw [h2]
      _ = (((V a).map (ra s a b)).comp ((U a).map (ra s a b))).comp ((V b).map (lb s a b)) := by
          rw [agreeU a b, Series.comp_assoc _ _ _ (constantCoeff_map_eq_zero hub.constantCoeff _)
            (constantCoeff_map_eq_zero hvb.constantCoeff _)]
      _ = (V b).map (lb s a b) := by rw [h1, Series.id_comp _ (constantCoeff_map_eq_zero hvb.constantCoeff _)]

  obtain ⟨u, hu⟩ := glue_series hf U agreeU
  obtain ⟨v, hv⟩ := glue_series hf V agreeV
  have hinj := jointlyInjective_algebraMap s hf
  have hinj' := jointlyInjective_reduceMap (p := p) (s := s) hf

  let Mtot : ℕ := ∑ i : Fin n, M ⟨f i, ⟨i, rfl⟩⟩
  have hMle : ∀ a : ↥s, M a ≤ Mtot := by
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact Finset.single_le_sum (f := fun i : Fin n => M ⟨f i, ⟨i, rfl⟩⟩) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hU : ∀ a : ↥s, IsODHom (t.X.map (algebraMap B (Localization.Away a.1)))
      (t'.X.map (algebraMap B (Localization.Away a.1))) (u.map (algebraMap B (Localization.Away a.1))) :=
    fun a => by rw [hu a]; exact (hW a).1
  have hV : ∀ a : ↥s, IsODHom (t'.X.map (algebraMap B (Localization.Away a.1)))
      (t.X.map (algebraMap B (Localization.Away a.1))) (v.map (algebraMap B (Localization.Away a.1))) :=
    fun a => by rw [hv a]; exact (hW a).2.1
  have hou : IsODHom t.X t'.X u := isODHom_of_forall_map hinj t.X t'.X u hU
  have hov : IsODHom t'.X t.X v := isODHom_of_forall_map hinj t'.X t.X v hV
  refine (isIsomorphic_iff t t').mpr ⟨u, v, Mtot, hou, hov, ?_, ?_, ?_⟩
  · apply hinj.series_eq
    intro a
    rw [Series.map_comp _ _ _ hou.constantCoeff, hu a, hv a, Series.map_id]
    exact (hW a).2.2.1
  · apply hinj.series_eq
    intro a
    rw [Series.map_comp _ _ _ hov.constantCoeff, hu a, hv a, Series.map_id]
    exact (hW a).2.2.2.1
  · apply hinj'.series_eq
    intro a
    rw [map_clause_lhs t t' hρ u hou.constantCoeff, map_clause_rhs t' hρ', hu a]
    have hc := (hW a).2.2.2.2
    have := compat_pad _ _ (hρa a) (hρa' a) (U a) (hW a).1 (M a) (Mtot - M a) hc
    rw [Nat.sub_add_cancel (hMle a)] at this
    simp only [Rigidified.map_n] at this ⊢
    exact this

end main

end DescGlue

end

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (ι : Zp2 p →+* O) {B : Type u} [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) [IsNoetherianRing B]
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (hloc : ∀ i, (t.map (algebraMap B (Localization.Away (f i)))).IsIsomorphic
      (t'.map (algebraMap B (Localization.Away (f i))))) :
    t.IsIsomorphic t' :=
  DescGlue.desc ι ψ hB t t' ht ht' n f hf hloc
    (fun B₁ _ g _ => CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ g t ht)

end S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_forall_isIsomorphic_map_localizationAway
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_forall_isIsomorphic_map_localizationAway (solution)
