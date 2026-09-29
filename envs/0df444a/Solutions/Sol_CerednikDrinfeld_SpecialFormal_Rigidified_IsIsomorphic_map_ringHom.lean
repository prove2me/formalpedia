-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsIsomorphic.map_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6be15322-9331-576d-ab72-771f9a1139a7

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom

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

end

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B B' : Type u} [CommRing B] [CommRing B'] (g : B →+* B') (t t' : Rigidified p Φ B)
    (hρ : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (h : t.IsIsomorphic t') : (t.map g).IsIsomorphic (t'.map g) :=
  DescGlue.IsIsomorphic.map hρ hρ' h g

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom (solution)
