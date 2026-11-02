-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_2_72
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:32:03.644049+00:00
-- url     : https://prove2.me/submissions/937b2b00-056c-4db9-9008-9bd423ba7541

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_Spaces
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Sober
import Mathlib.Order.Heyting.Regular
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Heyting.Hom
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Order.Ideal
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.CategoryTheory.Equivalence

noncomputable section


section Gelfand272Component1

set_option autoImplicit false
namespace Gelfand272
open CategoryTheory TopologicalSpace GelfandVNA.Duality
universe u

theorem open_comap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (hf : IsOpenMap f) : IsOpenFrameHom (Opens.comap f) := by
  constructor
  · intro S
    apply le_antisymm
    · apply le_sInf
      rintro _ ⟨U,hU,rfl⟩
      exact Opens.comap_mono f (sInf_le hU)
    · let V : Opens X := sInf (Opens.comap f '' S)
      have hV : (⟨f '' (V : Set X),hf _ V.isOpen⟩ : Opens Y) ≤ sInf S := by
        apply le_sInf
        intro U hU
        rintro _ ⟨x,hx,rfl⟩
        exact (sInf_le (Set.mem_image_of_mem (Opens.comap f) hU) : V ≤ Opens.comap f U) hx
      intro x hx
      exact hV ⟨x,hx,rfl⟩
  · intro U V
    apply Opens.ext
    simp only [Opens.coe_comap,Opens.coe_himp,
      hf.preimage_interior_eq_interior_preimage f.continuous,
      BooleanAlgebra.himp_eq,Set.sup_eq_union,Set.preimage_union,Set.preimage_compl]

def omega : HStonean.{u} ⥤ HStoneanLoc.{u} where
  obj S := ⟨Opens S.toTop,S.hyperstonean⟩
  map f := ⟨Opens.comap f.1,open_comap f.1 f.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem omega_forget : omega ⋙ HStoneanLoc.toLocale = HStonean.toTopFunctor ⋙ topToLocale := rfl

end Gelfand272
end Gelfand272Component1


section Gelfand272Component2

set_option autoImplicit false
open Set Filter TopologicalSpace
open GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

universe u

namespace Gelfand272Space

variable {X : Type*} [TopologicalSpace X]

lemma coe_pseudocompl (a : Opens X) :
    ((aᶜ : Opens X) : Set X) = (closure (a : Set X))ᶜ := by
  rw [Opens.coe_compl_eq_interior_compl, _root_.interior_compl]

lemma closure_subset_of_compl_sup (a b : Opens X) (h : bᶜ ⊔ a = ⊤) :
    closure (b : Set X) ⊆ (a : Set X) := by
  intro x hx
  have hm : x ∈ (bᶜ ⊔ a : Opens X) := by rw [h]; trivial
  rcases Opens.mem_sup.mp hm with hb | ha
  · have hn : x ∈ (closure (b : Set X))ᶜ := by
      rw [← coe_pseudocompl b]
      exact hb
    exact False.elim (hn hx)
  · exact ha

theorem regularSpace_of_regularLocale (h : IsRegularLocale (Opens X)) : RegularSpace X := by
  apply RegularSpace.of_exists_mem_nhds_isClosed_subset
  intro x s hs
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hs
  let a : Opens X := ⟨U, hU⟩
  have hx : x ∈ a := hxU
  rw [h a] at hx
  obtain ⟨b, hb, hxb⟩ := Opens.mem_sSup.mp hx
  refine ⟨closure (b : Set X), ?_, isClosed_closure, ?_⟩
  · exact mem_of_superset (b.isOpen.mem_nhds hxb) subset_closure
  · exact (closure_subset_of_compl_sup a b hb).trans hUs

theorem extremallyDisconnected_of_opens (h : ∀ a : Opens X, aᶜ ⊔ aᶜᶜ = ⊤) :
    ExtremallyDisconnected X := by
  constructor
  intro U hU
  let a : Opens X := ⟨U, hU⟩
  have hle : ((aᶜᶜ : Opens X) : Set X) ⊆ closure (a : Set X) := by
    rw [Opens.coe_compl_eq_interior_compl, coe_pseudocompl a, compl_compl]
    exact interior_subset
  have heq : closure (a : Set X) = ((aᶜᶜ : Opens X) : Set X) :=
    subset_antisymm (closure_subset_of_compl_sup (aᶜᶜ) a (h a)) hle
  change IsOpen (closure (a : Set X))
  rw [heq]
  exact (aᶜᶜ).isOpen

theorem hstonean_compact (S : HStonean.{u}) : CompactSpace S.toTop := by
  apply isCompact_univ_iff.mp
  exact (Opens.isCompactElement_iff (⊤ : Opens S.toTop)).mp S.hyperstonean.1.1.1.1

theorem hstonean_regular (S : HStonean.{u}) : RegularSpace S.toTop :=
  regularSpace_of_regularLocale S.hyperstonean.1.1.2

theorem hstonean_t2 (S : HStonean.{u}) : T2Space S.toTop := by
  letI : RegularSpace S.toTop := hstonean_regular S
  infer_instance

theorem hstonean_extremallyDisconnected (S : HStonean.{u}) :
    ExtremallyDisconnected S.toTop :=
  extremallyDisconnected_of_opens S.hyperstonean.1.2

end Gelfand272Space
end Gelfand272Component2


section Gelfand272Component3

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory
open GelfandVNA.Duality

universe u v

namespace Gelfand272FullFaithful

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def missedOpen (f : FrameHom (Opens Y) (Opens X)) (x : X) : Opens Y :=
  sSup {U : Opens Y | x ∉ f U}

def pointClosed (f : FrameHom (Opens Y) (Opens X)) (x : X) : Set Y :=
  (missedOpen f x : Set Y)ᶜ

lemma missedOpen_not_mem (f : FrameHom (Opens Y) (Opens X)) (x : X) :
    x ∉ f (missedOpen f x) := by
  rw [missedOpen, map_sSup]
  intro hx
  obtain ⟨V, ⟨U, hU, rfl⟩, hxU⟩ := Opens.mem_sSup.mp hx
  exact hU hxU

lemma pointClosed_isClosed (f : FrameHom (Opens Y) (Opens X)) (x : X) :
    IsClosed (pointClosed f x) :=
  (missedOpen f x).isOpen.isClosed_compl

lemma pointClosed_inter_iff (f : FrameHom (Opens Y) (Opens X)) (x : X) (U : Opens Y) :
    (pointClosed f x ∩ (U : Set Y)).Nonempty ↔ x ∈ f U := by
  classical
  constructor
  · rintro ⟨y, hyC, hyU⟩
    by_contra hx
    exact hyC ((le_sSup hx : U ≤ missedOpen f x) hyU)
  · intro hx
    by_contra hnone
    have hU : U ≤ missedOpen f x := by
      intro y hyU
      by_contra hy
      exact hnone ⟨y, hy, hyU⟩
    exact missedOpen_not_mem f x (OrderHomClass.mono f hU hx)

lemma pointClosed_irreducible (f : FrameHom (Opens Y) (Opens X)) (x : X) :
    IsIrreducible (pointClosed f x) := by
  constructor
  · have hx : x ∈ f (⊤ : Opens Y) := by rw [map_top]; trivial
    simpa only [Opens.coe_top, inter_univ] using (pointClosed_inter_iff f x ⊤).mpr hx
  · intro U V hU hV hCU hCV
    have hxU : x ∈ f (⟨U, hU⟩ : Opens Y) :=
      (pointClosed_inter_iff f x ⟨U, hU⟩).mp hCU
    have hxV : x ∈ f (⟨V, hV⟩ : Opens Y) :=
      (pointClosed_inter_iff f x ⟨V, hV⟩).mp hCV
    have hxUV : x ∈ f ((⟨U, hU⟩ : Opens Y) ⊓ ⟨V, hV⟩) := by
      rw [map_inf]
      exact ⟨hxU, hxV⟩
    exact (pointClosed_inter_iff f x ((⟨U, hU⟩ : Opens Y) ⊓ ⟨V, hV⟩)).mpr hxUV

def pointOfFrameHom [QuasiSober Y] (f : FrameHom (Opens Y) (Opens X)) (x : X) : Y :=
  (pointClosed_irreducible f x).genericPoint

lemma pointOfFrameHom_mem [QuasiSober Y] (f : FrameHom (Opens Y) (Opens X))
    (x : X) (U : Opens Y) : pointOfFrameHom f x ∈ U ↔ x ∈ f U := by
  have hg := (pointClosed_irreducible f x).isGenericPoint_genericPoint (pointClosed_isClosed f x)
  exact (hg.mem_open_set_iff U.isOpen).trans (pointClosed_inter_iff f x U)

def continuousMapOfFrameHom [QuasiSober Y] (f : FrameHom (Opens Y) (Opens X)) : C(X, Y) where
  toFun := pointOfFrameHom f
  continuous_toFun := by
    apply continuous_def.mpr
    intro U hU
    have heq : pointOfFrameHom f ⁻¹' U = (f (⟨U, hU⟩ : Opens Y) : Set X) :=
      Set.ext (fun x => pointOfFrameHom_mem f x ⟨U, hU⟩)
    rw [heq]
    exact (f ⟨U, hU⟩).isOpen

theorem continuousMapOfFrameHom_comap [QuasiSober Y] (f : FrameHom (Opens Y) (Opens X)) :
    Opens.comap (continuousMapOfFrameHom f) = f := by
  apply FrameHom.ext
  intro U
  apply Opens.ext
  exact Set.ext (fun x => pointOfFrameHom_mem f x U)

theorem continuousMapOfFrameHom_unique [QuasiSober Y] [T0Space Y]
    (f : FrameHom (Opens Y) (Opens X)) (g : C(X, Y)) (hg : Opens.comap g = f) :
    g = continuousMapOfFrameHom f :=
  Opens.comap_injective (hg.trans (continuousMapOfFrameHom_comap f).symm)

theorem exists_unique_continuousMap [QuasiSober Y] [T0Space Y]
    (f : FrameHom (Opens Y) (Opens X)) : ∃! g : C(X, Y), Opens.comap g = f :=
  ⟨continuousMapOfFrameHom f, continuousMapOfFrameHom_comap f,
    fun g hg => continuousMapOfFrameHom_unique f g hg⟩

theorem isOpenMap_of_comap_sInf [T1Space Y] (g : C(X, Y))
    (h : ∀ s : Set (Opens Y), Opens.comap g (sInf s) = sInf (Opens.comap g '' s)) :
    IsOpenMap g := by
  classical
  intro U hU
  let a : Opens X := ⟨U, hU⟩
  let s : Set (Opens Y) := {V | g '' U ⊆ (V : Set Y)}
  let b : Opens Y := sInf s
  have hab : a ≤ Opens.comap g b := by
    change a ≤ Opens.comap g (sInf s)
    rw [h s]
    apply le_sInf
    rintro W ⟨V, hV, rfl⟩
    intro x hx
    exact hV ⟨x, hx, rfl⟩
  have heq : g '' U = (b : Set Y) := by
    apply subset_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hab hx
    · intro y hyb
      by_contra hy
      let V : Opens Y := ⟨{y}ᶜ, isClosed_singleton.isOpen_compl⟩
      have hV : V ∈ s := by
        intro z hz
        change z ∉ ({y} : Set Y)
        intro hzy
        have heq : z = y := Set.mem_singleton_iff.mp hzy
        subst z
        exact hy hz
      have hyV : y ∈ V := (sInf_le hV : b ≤ V) hyb
      exact hyV (by rfl)
  rw [heq]
  exact b.isOpen

def openMapOfFrameHom (S T : HStonean.{u})
    (f : FrameHom (Opens T.toTop) (Opens S.toTop)) (hf : IsOpenFrameHom f) : S ⟶ T :=
  ⟨continuousMapOfFrameHom f, by
    letI : T2Space T.toTop := Gelfand272Space.hstonean_t2 T
    apply isOpenMap_of_comap_sInf
    intro s
    rw [continuousMapOfFrameHom_comap]
    exact hf.1 s⟩

instance omega_full : (Gelfand272.omega.{u}).Full where
  map_surjective {S T} f := by
    refine ⟨openMapOfFrameHom S T f.1 f.2, ?_⟩
    apply Subtype.ext
    exact continuousMapOfFrameHom_comap f.1

instance omega_faithful : (Gelfand272.omega.{u}).Faithful where
  map_injective := by
    intro S T f g h
    apply Subtype.ext
    apply Opens.comap_injective
    exact congrArg Subtype.val h

end Gelfand272FullFaithful
end Gelfand272Component3


section Gelfand272Component4
/- Helpers reproduced from our accepted lemma2.58 solution, unchanged. -/

set_option autoImplicit false

open Set Filter QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand258Work

variable {L : Type*} [Order.Frame L]

theorem compact_regular (hL : IsStoneanLocale L) {a : L} (ha : IsCompactElement a) :
    Heyting.IsRegular a := by
  let s : Set L := {b | bᶜ ⊔ a = ⊤}
  have hs : s.Nonempty := ⟨⊥, by simp [s]⟩
  have hd : DirectedOn (· ≤ ·) s := by
    intro b hb c hc
    refine ⟨b ⊔ c, ?_, le_sup_left, le_sup_right⟩
    change (b ⊔ c)ᶜ ⊔ a = ⊤
    change bᶜ ⊔ a = ⊤ at hb
    change cᶜ ⊔ a = ⊤ at hc
    simp only [compl_sup, sup_inf_right, hb, hc, inf_top_eq]
  have heq : a = sSup s := hL.1.2 a
  have hlub : IsLUB s a := heq.symm ▸ isLUB_sSup s
  obtain ⟨b, hb, hab⟩ := ha s a hs hd hlub le_rfl
  have hcomp : aᶜ ⊔ a = ⊤ := by
    apply top_le_iff.mp
    change bᶜ ⊔ a = ⊤ at hb
    rw [← hb]
    exact sup_le_sup_right (compl_anti hab) a
  exact (IsCompl.of_eq compl_inf_eq_bot hcomp).compl_eq

theorem regular_compact (hL : IsStoneanLocale L) {a : L} (ha : Heyting.IsRegular a) :
    IsCompactElement a := by
  have hac : a ⊔ aᶜ = ⊤ := by
    simpa only [ha.eq, sup_comm] using hL.2 a
  intro s u hs hd hlu hau
  let f : L → L := fun x => x ⊔ aᶜ
  have hf : Monotone f := fun _ _ h => sup_le_sup_right h _
  have hdi : DirectedOn (· ≤ ·) (f '' s) := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
    exact ⟨f d, ⟨d, hd, rfl⟩, hf hbd, hf hcd⟩
  have hli : IsLUB (f '' s) (u ⊔ aᶜ) := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact sup_le_sup_right (hlu.1 hx) _
    · intro b hb
      apply sup_le
      · apply hlu.2
        intro x hx
        exact le_sup_left.trans (hb ⟨x, hx, rfl⟩)
      · obtain ⟨x, hx⟩ := hs
        exact le_sup_right.trans (hb ⟨x, hx, rfl⟩)
  have htop : (⊤ : L) ≤ u ⊔ aᶜ := by
    rw [← hac]
    exact sup_le_sup_right hau _
  obtain ⟨_, ⟨x, hx, rfl⟩, hlarge⟩ := hL.1.1.1 (f '' s) (u ⊔ aᶜ)
    (hs.image f) hdi hli htop
  refine ⟨x, hx, ?_⟩
  calc
    a = a ⊓ ⊤ := by simp
    _ ≤ a ⊓ (x ⊔ aᶜ) := inf_le_inf_left a hlarge
    _ = a ⊓ x := by rw [inf_sup_left, inf_compl_eq_bot, sup_bot_eq]
    _ ≤ x := inf_le_right

def compactRegularIso (hL : IsStoneanLocale L) :
    {a : L // IsCompactElement a} ≃o Heyting.Regular L where
  toFun a := ⟨a.1, compact_regular hL a.2⟩
  invFun a := ⟨a.1, regular_compact hL a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem continuous_comp {A B R : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    [Zero R] [Add R] [TopologicalSpace R]
    (f : A → B) (hm : Monotone f) (hbot : f ⊥ = ⊥)
    (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (hinf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (hlub : ∀ (s : Set A) (a : A), IsLUB s a → IsLUB (f '' s) (f a))
    (ν : B → R) (hν : IsContinuousValuation ν) :
    IsContinuousValuation (ν ∘ f) := by
  constructor
  · constructor
    · simpa only [Function.comp_apply, hbot] using hν.1.1
    · intro a b
      simpa only [Function.comp_apply, hsup, hinf] using hν.1.2 (f a) (f b)
  · intro s a hs hd hsa
    have hdi : DirectedOn (· ≤ ·) (f '' s) := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨f d, ⟨d, hd, rfl⟩, hm hbd, hm hcd⟩
    let g : s → f '' s := fun b => ⟨f b.1, ⟨b.1, b.2, rfl⟩⟩
    have hgm : Monotone g := fun _ _ h => hm h
    have hgt : Tendsto g atTop atTop := hgm.tendsto_atTop_atTop (by
      rintro ⟨b, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, le_rfl⟩)
    exact (hν.2 (f '' s) (f a) (hs.image f) hdi (hlub s a hsa)).comp hgt

open Heyting.Regular

theorem regularize_inf (a b : L) : toRegular (a ⊓ b) = toRegular a ⊓ toRegular b := by
  apply coe_injective
  exact compl_compl_inf_distrib a b

theorem regularize_normal {R : Type*} [Zero R] [Add R] [TopologicalSpace R]
    (μ : Heyting.Regular L → R) (hμ : IsContinuousValuation μ) :
    IsNormalValuation (fun a => μ (toRegular a)) := by
  constructor
  · exact continuous_comp toRegular toRegular.monotone (by
      apply coe_injective
      simp) (fun _ _ => gi.gc.l_sup) regularize_inf
      (fun _ _ h => gi.gc.isLUB_l_image h) μ hμ
  · intro a
    apply congrArg μ
    apply coe_injective
    exact compl_compl_compl aᶜ

theorem restriction_continuous {R : Type*} [Zero R] [Add R] [TopologicalSpace R]
    (ν : L → R) (hν : IsNormalValuation ν) :
    IsContinuousValuation (fun a : Heyting.Regular L => ν a) := by
  constructor
  · constructor
    · exact hν.1.1.1
    · intro a b
      change ν (a : L) + ν (b : L) = ν ((a : L) ⊔ b)ᶜᶜ + ν ((a : L) ⊓ b)
      rw [hν.2]
      exact hν.1.1.2 (a : L) (b : L)
  · intro s a hs hd hsa
    let t : Set L := ((↑) : Heyting.Regular L → L) '' s
    have ht : t.Nonempty := hs.image _
    have hdt : DirectedOn (· ≤ ·) t := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨d, ⟨d, hd, rfl⟩, hbd, hcd⟩
    have himage : toRegular '' t = s := by
      simp [t, Set.image_image, Function.comp_def]
    have hlu := gi.gc.isLUB_l_image (isLUB_sSup t)
    rw [himage] at hlu
    have hqa : toRegular (sSup t) = a := hlu.unique hsa
    have hv : ν (sSup t) = ν (a : L) := by
      calc
        ν (sSup t) = ν (sSup t)ᶜᶜ := (hν.2 _).symm
        _ = ν (a : L) := congrArg ν (congrArg ((↑) : Heyting.Regular L → L) hqa)
    let g : s → t := fun b => ⟨b.1, ⟨b.1, b.2, rfl⟩⟩
    have hgm : Monotone g := fun _ _ h => h
    have hgt : Tendsto g atTop atTop := hgm.tendsto_atTop_atTop (by
      rintro ⟨_, b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, le_rfl⟩)
    have hc := (hν.1.2 t (sSup t) ht hdt (isLUB_sSup t)).comp hgt
    rw [hv] at hc
    exact hc

theorem iso_continuous {A B R : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    [Zero R] [Add R] [TopologicalSpace R]
    (e : A ≃o B) (ν : B → R) (hν : IsContinuousValuation ν) :
    IsContinuousValuation (ν ∘ e) :=
  continuous_comp e e.monotone e.map_bot e.map_sup e.map_inf
    (fun _ _ h => e.isLUB_image'.2 h) ν hν

theorem continuous_extension {R B : Type*} [Zero R] [Add R] [TopologicalSpace R]
    [Lattice B] [OrderBot B] (hL : IsStoneanLocale L)
    (e : B ≃o {a : L // IsCompactElement a}) :
    (∀ ν : L → R, IsNormalValuation ν → IsContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → R, IsContinuousValuation μ →
      ∃! ν : L → R, IsNormalValuation ν ∧ ∀ b, ν (e b) = μ b) := by
  let er : B ≃o Heyting.Regular L := e.trans (compactRegularIso hL)
  have hcoe (b : B) : (er b : L) = e b := rfl
  have hback (a : Heyting.Regular L) : (e (er.symm a) : L) = a := by
    rw [← hcoe, er.apply_symm_apply]
  constructor
  · intro ν hν
    exact iso_continuous er _ (restriction_continuous ν hν)
  · intro μ hμ
    let ν : L → R := fun a => μ (er.symm (toRegular a))
    refine ⟨ν, ⟨regularize_normal _ (iso_continuous er.symm μ hμ), ?_⟩, ?_⟩
    · intro b
      change μ (er.symm (toRegular (e b : L))) = μ b
      rw [← hcoe, toRegular_coe, er.symm_apply_apply]
    · intro ξ hξ
      funext a
      calc
        ξ a = ξ aᶜᶜ := (hξ.1.2 a).symm
        _ = ξ (e (er.symm (toRegular a))) := congrArg ξ (hback (toRegular a)).symm
        _ = μ (er.symm (toRegular a)) := hξ.2 _
        _ = ν a := rfl

theorem positive_comp {A B : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    (f : A → B) (hm : Monotone f) (hbot : f ⊥ = ⊥)
    (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (hinf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (hlub : ∀ (s : Set A) (a : A), IsLUB s a → IsLUB (f '' s) (f a))
    (ν : B → NNReal) (hν : IsPositiveContinuousValuation ν) :
    IsPositiveContinuousValuation (ν ∘ f) := by
  refine ⟨⟨?_, ?_⟩, hν.2.1.comp hm, ?_⟩
  · simpa only [Function.comp_apply, hbot] using hν.1.1
  · intro a b
    simpa only [Function.comp_apply, hsup, hinf] using hν.1.2 (f a) (f b)
  · intro s a hs hd hsa
    have hdi : DirectedOn (· ≤ ·) (f '' s) := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨f d, ⟨d, hd, rfl⟩, hm hbd, hm hcd⟩
    simpa only [Set.image_image, Function.comp_def] using
      hν.2.2 (f '' s) (f a) (hs.image f) hdi (hlub s a hsa)

theorem regularize_positive_normal (μ : Heyting.Regular L → NNReal)
    (hμ : IsPositiveContinuousValuation μ) :
    IsPositiveNormalValuation (fun a => μ (toRegular a)) := by
  constructor
  · exact positive_comp toRegular toRegular.monotone (by
      apply coe_injective
      simp) (fun _ _ => gi.gc.l_sup) regularize_inf
      (fun _ _ h => gi.gc.isLUB_l_image h) μ hμ
  · intro a
    apply congrArg μ
    apply coe_injective
    exact compl_compl_compl aᶜ

theorem restriction_positive_continuous (ν : L → NNReal)
    (hν : IsPositiveNormalValuation ν) :
    IsPositiveContinuousValuation (fun a : Heyting.Regular L => ν a) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact hν.1.1.1
  · intro a b
    change ν (a : L) + ν (b : L) = ν ((a : L) ⊔ b)ᶜᶜ + ν ((a : L) ⊓ b)
    rw [hν.2]
    exact hν.1.1.2 (a : L) (b : L)
  · intro a b h
    exact hν.1.2.1 h
  · intro s a hs hd hsa
    let t : Set L := ((↑) : Heyting.Regular L → L) '' s
    have ht : t.Nonempty := hs.image _
    have hdt : DirectedOn (· ≤ ·) t := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨d, ⟨d, hd, rfl⟩, hbd, hcd⟩
    have himage : toRegular '' t = s := by
      simp [t, Set.image_image, Function.comp_def]
    have hlu := gi.gc.isLUB_l_image (isLUB_sSup t)
    rw [himage] at hlu
    have hqa : toRegular (sSup t) = a := hlu.unique hsa
    have hv : ν (sSup t) = ν (a : L) := by
      calc
        ν (sSup t) = ν (sSup t)ᶜᶜ := (hν.2 _).symm
        _ = ν (a : L) := congrArg ν (congrArg ((↑) : Heyting.Regular L → L) hqa)
    simpa only [t, Set.image_image, Function.comp_def, hv] using
      hν.1.2.2 t (sSup t) ht hdt (isLUB_sSup t)

theorem iso_positive_continuous {A B : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    (e : A ≃o B) (ν : B → NNReal) (hν : IsPositiveContinuousValuation ν) :
    IsPositiveContinuousValuation (ν ∘ e) :=
  positive_comp e e.monotone e.map_bot e.map_sup e.map_inf
    (fun _ _ h => e.isLUB_image'.2 h) ν hν

theorem positive_extension {B : Type*} [Lattice B] [OrderBot B]
    (hL : IsStoneanLocale L) (e : B ≃o {a : L // IsCompactElement a}) :
    (∀ ν : L → NNReal, IsPositiveNormalValuation ν →
      IsPositiveContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → NNReal, IsPositiveContinuousValuation μ →
      ∃! ν : L → NNReal, IsPositiveNormalValuation ν ∧ ∀ b, ν (e b) = μ b) := by
  let er : B ≃o Heyting.Regular L := e.trans (compactRegularIso hL)
  have hcoe (b : B) : (er b : L) = e b := rfl
  have hback (a : Heyting.Regular L) : (e (er.symm a) : L) = a := by
    rw [← hcoe, er.apply_symm_apply]
  constructor
  · intro ν hν
    exact iso_positive_continuous er _ (restriction_positive_continuous ν hν)
  · intro μ hμ
    let ν : L → NNReal := fun a => μ (er.symm (toRegular a))
    refine ⟨ν, ⟨regularize_positive_normal _ (iso_positive_continuous er.symm μ hμ), ?_⟩, ?_⟩
    · intro b
      change μ (er.symm (toRegular (e b : L))) = μ b
      rw [← hcoe, toRegular_coe, er.symm_apply_apply]
    · intro ξ hξ
      funext a
      calc
        ξ a = ξ aᶜᶜ := (hξ.1.2 a).symm
        _ = ξ (e (er.symm (toRegular a))) := congrArg ξ (hback (toRegular a)).symm
        _ = μ (er.symm (toRegular a)) := hξ.2 _
        _ = ν a := rfl

end Gelfand258Work
end Gelfand272Component4


section Gelfand272Component5

set_option autoImplicit false
open Set QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand272Transport

variable {L M : Type*} [Order.Frame L] [Order.Frame M]

theorem compactElement_map (e : L ≃o M) {a : L} (ha : IsCompactElement a) :
    IsCompactElement (e a) := by
  intro s b hs hd hlub hab
  have hd' : DirectedOn (· ≤ ·) (e.symm '' s) := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd', rfl⟩
    obtain ⟨z, hz, hcz, hdz⟩ := hd c hc d hd'
    exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.symm.monotone hcz, e.symm.monotone hdz⟩
  have ha' : a ≤ e.symm b := by
    simpa only [e.symm_apply_apply] using e.symm.monotone hab
  obtain ⟨c, ⟨d, hd, rfl⟩, had⟩ :=
    ha (e.symm '' s) (e.symm b) (hs.image e.symm) hd' (e.symm.isLUB_image'.2 hlub) ha'
  exact ⟨d, hd, by simpa only [e.apply_symm_apply] using e.monotone had⟩

theorem compactElement_iff (e : L ≃o M) (a : L) :
    IsCompactElement a ↔ IsCompactElement (e a) := by
  constructor
  · exact compactElement_map e
  · intro h
    simpa only [e.symm_apply_apply] using compactElement_map e.symm h

theorem coherent_map (e : L ≃o M) (h : IsCoherentLocale L) : IsCoherentLocale M := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e.map_top] using compactElement_map e h.1
  · intro a b ha hb
    have hc := compactElement_map e
      (h.2.1 (e.symm a) (e.symm b) (compactElement_map e.symm ha) (compactElement_map e.symm hb))
    simpa only [e.map_inf, e.apply_symm_apply] using hc
  · intro a
    calc
      a = e (sSup {b : L | IsCompactElement b ∧ b ≤ e.symm a}) := by
        rw [← h.2.2 (e.symm a), e.apply_symm_apply]
      _ = sSup (e '' {b : L | IsCompactElement b ∧ b ≤ e.symm a}) := map_sSup e _
      _ = sSup {b : M | IsCompactElement b ∧ b ≤ a} := by
        apply congrArg sSup
        ext b
        constructor
        · rintro ⟨c, ⟨hc, hca⟩, rfl⟩
          exact ⟨compactElement_map e hc, by simpa only [e.apply_symm_apply] using e.monotone hca⟩
        · rintro ⟨hb, hba⟩
          exact ⟨e.symm b, ⟨compactElement_map e.symm hb, e.symm.monotone hba⟩,
            e.apply_symm_apply b⟩

theorem regular_map (e : L ≃o M) (h : IsRegularLocale L) : IsRegularLocale M := by
  intro a
  calc
    a = e (sSup {b : L | bᶜ ⊔ e.symm a = ⊤}) := by
      rw [← h (e.symm a), e.apply_symm_apply]
    _ = sSup (e '' {b : L | bᶜ ⊔ e.symm a = ⊤}) := map_sSup e _
    _ = sSup {b : M | bᶜ ⊔ a = ⊤} := by
      apply congrArg sSup
      ext b
      constructor
      · rintro ⟨c, hc, rfl⟩
        change (e c)ᶜ ⊔ a = ⊤
        simpa only [map_sup, map_compl, e.apply_symm_apply, map_top] using congrArg e hc
      · intro hb
        refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
        change (e.symm b)ᶜ ⊔ e.symm a = ⊤
        simpa only [map_sup, map_compl, map_top] using congrArg e.symm hb

theorem stonean_map (e : L ≃o M) (h : IsStoneanLocale L) : IsStoneanLocale M := by
  refine ⟨⟨coherent_map e h.1.1, regular_map e h.1.2⟩, ?_⟩
  intro a
  simpa only [map_sup, map_compl, e.apply_symm_apply, map_top] using
    congrArg e (h.2 (e.symm a))

theorem positiveNormal_comp (e : L ≃o M) (ν : M → NNReal)
    (hν : IsPositiveNormalValuation ν) : IsPositiveNormalValuation (ν ∘ e) := by
  refine ⟨Gelfand258Work.iso_positive_continuous e ν hν.1, ?_⟩
  intro a
  change ν (e aᶜᶜ) = ν (e a)
  rw [map_compl, map_compl, hν.2]

theorem hyperstonean_map (e : L ≃o M) (h : IsHyperstoneanLocale L) :
    IsHyperstoneanLocale M := by
  refine ⟨stonean_map e h.1, ?_⟩
  intro a ha
  have ha' : e.symm a ≠ ⊥ := by
    intro heq
    apply ha
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e ⊥ := congrArg e heq
      _ = ⊥ := e.map_bot
  obtain ⟨ν, hν, hνa⟩ := h.2 (e.symm a) ha'
  exact ⟨ν ∘ e.symm, positiveNormal_comp e.symm ν hν, hνa⟩

theorem hyperstonean_iff (e : L ≃o M) : IsHyperstoneanLocale L ↔ IsHyperstoneanLocale M :=
  ⟨hyperstonean_map e, hyperstonean_map e.symm⟩

theorem coherent_iff (e : L ≃o M) : IsCoherentLocale L ↔ IsCoherentLocale M :=
  ⟨coherent_map e, coherent_map e.symm⟩

theorem regular_iff (e : L ≃o M) : IsRegularLocale L ↔ IsRegularLocale M :=
  ⟨regular_map e, regular_map e.symm⟩

theorem stonean_iff (e : L ≃o M) : IsStoneanLocale L ↔ IsStoneanLocale M :=
  ⟨stonean_map e, stonean_map e.symm⟩

end Gelfand272Transport
end Gelfand272Component5


section Gelfand272Component6

set_option autoImplicit false
open CategoryTheory GelfandVNA.Duality

universe u

namespace Gelfand272Transport

def frameHomOfOrderIso {L M : Type u} [Order.Frame L] [Order.Frame M]
    (e : L ≃o M) : FrameHom L M := e

theorem orderIso_isOpenFrameHom {L M : Type u} [Order.Frame L] [Order.Frame M]
    (e : L ≃o M) : IsOpenFrameHom (frameHomOfOrderIso e) := by
  constructor
  · intro s
    change e (sInf s) = sInf (e '' s)
    exact map_sInf e s
  · intro a b
    change e (a ⇨ b) = e a ⇨ e b
    exact map_himp e a b

def localeIso {A B : HStoneanLoc.{u}} (e : A.carrier ≃o B.carrier) : A ≅ B where
  hom := ⟨frameHomOfOrderIso e.symm, orderIso_isOpenFrameHom e.symm⟩
  inv := ⟨frameHomOfOrderIso e, orderIso_isOpenFrameHom e⟩
  hom_inv_id := by
    apply Subtype.ext
    apply FrameHom.ext
    intro a
    exact e.symm_apply_apply a
  inv_hom_id := by
    apply Subtype.ext
    apply FrameHom.ext
    intro b
    exact e.apply_symm_apply b

end Gelfand272Transport
end Gelfand272Component6


section Gelfand272Component7

set_option autoImplicit false
namespace Gelfand272Spectrum
open TopologicalSpace
universe u
variable (B : Type u) [BooleanAlgebra B]

def idempotentIso : B ≃o {r : AsBoolRing B // IsIdempotentElem r} where
  toFun b := ⟨toBoolRing b,BooleanRing.isIdempotentElem _⟩
  invFun r := ofBoolRing r.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := by
    intro a b
    change a ⊓ b = a ↔ a ≤ b
    exact inf_eq_left

noncomputable def clopensIso : B ≃o Clopens (PrimeSpectrum (AsBoolRing B)) :=
  (idempotentIso B).trans PrimeSpectrum.isIdempotentElemEquivClopens

noncomputable def basis (b : B) : Opens (PrimeSpectrum (AsBoolRing B)) :=
  (clopensIso B b).toOpens

theorem basis_eq_basicOpen (b : B) : basis B b = PrimeSpectrum.basicOpen (toBoolRing b) := rfl

theorem basis_le_iff (a b : B) : basis B a ≤ basis B b ↔ a ≤ b := by
  change clopensIso B a ≤ clopensIso B b ↔ a ≤ b
  exact (clopensIso B).le_iff_le

noncomputable def basisEmbedding : B ↪o Opens (PrimeSpectrum (AsBoolRing B)) where
  toFun := basis B
  inj' := by
    intro a b h
    exact le_antisymm ((basis_le_iff B a b).mp h.le) ((basis_le_iff B b a).mp h.ge)
  map_rel_iff' := fun {a b} => basis_le_iff B a b

theorem basis_bot : basis B ⊥ = ⊥ := by
  change (clopensIso B ⊥).toOpens = ⊥
  rw [map_bot]
  rfl

theorem basis_sup (a b : B) : basis B (a ⊔ b) = basis B a ⊔ basis B b := by
  change (clopensIso B (a ⊔ b)).toOpens = _
  rw [map_sup]
  rfl

theorem basis_compact (b : B) : IsCompactElement (basis B b) := by
  rw [basis_eq_basicOpen,Opens.isCompactElement_iff]
  exact PrimeSpectrum.isCompact_basicOpen _

theorem basis_density (U : Opens (PrimeSpectrum (AsBoolRing B))) :
    U = sSup (basis B '' {b | basis B b ≤ U}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨V,⟨r,rfl⟩,hxV,hVU⟩ :=
      (Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := AsBoolRing B))) hx
    have he : basis B (ofBoolRing r) = PrimeSpectrum.basicOpen r := by
      rw [basis_eq_basicOpen,toBoolRing_ofBoolRing]
    have hm : basis B (ofBoolRing r) ∈ basis B '' {b | basis B b ≤ U} := by
      refine ⟨ofBoolRing r,?_,rfl⟩
      change basis B (ofBoolRing r) ≤ U
      simpa only [he] using hVU
    exact (le_sSup hm) (by simpa only [he] using hxV)
  · apply sSup_le
    rintro _ ⟨b,hb,rfl⟩
    exact hb

end Gelfand272Spectrum
end Gelfand272Component7


section Gelfand272Component8

set_option autoImplicit false

open Set Order

namespace Gelfand273Ideal

universe u
variable {A : Type u}

section Frame
variable [DistribLattice A] [OrderBot A]

/-- The implication of ideals, as in Pavlov's Remark 2.30. -/
def idealHimp (I J : Ideal A) : Ideal A where
  carrier := {x | ∀ a ∈ I, x ⊓ a ∈ J}
  lower' := by
    intro x y hxy hy a ha
    exact J.lower (inf_le_inf_right a hxy) (hy a ha)
  nonempty' := ⟨⊥, by intro a ha; simpa using J.bot_mem⟩
  directed' := by
    intro x hx y hy
    refine ⟨x ⊔ y, ?_, le_sup_left, le_sup_right⟩
    intro a ha
    rw [inf_sup_right]
    exact Ideal.sup_mem (hx a ha) (hy a ha)

theorem idealHimp_gc (I : Ideal A) :
    GaloisConnection (fun J : Ideal A => I ⊓ J) (idealHimp I) := by
  intro J K
  constructor
  · intro h x hx a ha
    apply h
    exact ⟨I.lower inf_le_right ha, J.lower inf_le_left hx⟩
  · intro h x hx
    have hh := h hx.2 x hx.1
    simpa only [inf_idem] using hh

/-- The ideal completion of a bounded distributive lattice is a frame. -/
noncomputable instance idealFrame : Order.Frame (Ideal A) :=
  Order.Frame.ofMinimalAxioms
    { inf_sSup_le_iSup_inf := fun I s => by
        rw [(idealHimp_gc I).l_sSup] }

end Frame

section Compact
variable [SemilatticeSup A] [OrderBot A]

def directedUnion (s : Set (Ideal A)) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) :
    Ideal A where
  carrier := {x | ∃ I ∈ s, x ∈ I}
  lower' := by
    rintro x y hxy ⟨I, hI, hy⟩
    exact ⟨I, hI, I.lower hxy hy⟩
  nonempty' := by
    obtain ⟨I, hI⟩ := hs
    exact ⟨⊥, I, hI, I.bot_mem⟩
  directed' := by
    rintro x ⟨I, hI, hx⟩ y ⟨J, hJ, hy⟩
    obtain ⟨K, hK, hIK, hJK⟩ := hd I hI J hJ
    exact ⟨x ⊔ y, ⟨K, hK, Ideal.sup_mem (hIK hx) (hJK hy)⟩,
      le_sup_left, le_sup_right⟩

theorem sSup_eq_directedUnion (s : Set (Ideal A)) (hs : s.Nonempty)
    (hd : DirectedOn (· ≤ ·) s) : sSup s = directedUnion s hs hd := by
  apply le_antisymm
  · exact sSup_le fun I hI x hx => ⟨I, hI, hx⟩
  · rintro x ⟨I, hI, hx⟩
    exact (le_sSup hI : I ≤ sSup s) hx

theorem principal_compact (a : A) : IsCompactElement (Ideal.principal a) := by
  intro s I hs hd hlu haI
  rw [← hlu.sSup_eq, sSup_eq_directedUnion s hs hd] at haI
  obtain ⟨J, hJ, haJ⟩ := haI Ideal.mem_principal_self
  exact ⟨J, hJ, Ideal.principal_le_iff.mpr haJ⟩

theorem ideal_compact_iff_principal (I : Ideal A) :
    IsCompactElement I ↔ ∃ a : A, I = Ideal.principal a := by
  constructor
  · intro hc
    let s : Set (Ideal A) := Ideal.principal '' (I : Set A)
    have hs : s.Nonempty := I.nonempty.image _
    have hd : DirectedOn (· ≤ ·) s := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      refine ⟨Ideal.principal (a ⊔ b), ⟨a ⊔ b, Ideal.sup_mem ha hb, rfl⟩, ?_, ?_⟩
      · exact Ideal.principal_le_iff.mpr le_sup_left
      · exact Ideal.principal_le_iff.mpr le_sup_right
    have hlub : IsLUB s I := by
      constructor
      · rintro _ ⟨a, ha, rfl⟩
        exact Ideal.principal_le_iff.mpr ha
      · intro J hJ a ha
        exact hJ ⟨a, ha, rfl⟩ Ideal.mem_principal_self
    obtain ⟨_, ⟨a, ha, rfl⟩, hIa⟩ := hc s I hs hd hlub le_rfl
    exact ⟨a, hIa.antisymm (Ideal.principal_le_iff.mpr ha)⟩
  · rintro ⟨a, rfl⟩
    exact principal_compact a

/-- The counit on objects: compact ideals are precisely principal ideals. -/
noncomputable def principalCompactIso : A ≃o {I : Ideal A // IsCompactElement I} where
  toEquiv := Equiv.ofBijective (fun a => ⟨Ideal.principal a, principal_compact a⟩) (by
    constructor
    · intro a b h
      have he := congrArg Subtype.val h
      change Ideal.principal a = Ideal.principal b at he
      apply le_antisymm
      · exact Ideal.mem_principal.mp (Ideal.principal_le_iff.mp he.le)
      · exact Ideal.mem_principal.mp (Ideal.principal_le_iff.mp he.symm.le)
    · intro I
      obtain ⟨a, ha⟩ := (ideal_compact_iff_principal I.1).mp I.2
      exact ⟨a, Subtype.ext ha.symm⟩)
  map_rel_iff' := by
    intro a b
    exact Ideal.principal_le_iff.trans Ideal.mem_principal

end Compact
end Gelfand273Ideal

end Gelfand272Component8


section Gelfand272Component9

set_option autoImplicit false
open Set Order

namespace Gelfand273Ideal

universe u v
variable {B : Type u} {L : Type v} [SemilatticeSup B] [OrderBot B] [CompleteLattice L]

/-- The ideal of compact basis elements below an element. -/
def basisIdeal (k : B ↪o L) (hbot : k ⊥ = ⊥)
    (hsup : ∀ a b, k (a ⊔ b) = k a ⊔ k b) (a : L) : Ideal B where
  carrier := {b | k b ≤ a}
  lower' := fun _ _ hxy hy => (k.monotone hxy).trans hy
  nonempty' := ⟨⊥, by change k ⊥ ≤ a; rw [hbot]; exact bot_le⟩
  directed' := by
    intro b hb c hc
    refine ⟨b ⊔ c, ?_, le_sup_left, le_sup_right⟩
    change k (b ⊔ c) ≤ a
    rw [hsup]
    exact sup_le hb hc

/-- An algebraic complete lattice is the ideal completion of any compact basis
closed under bottom and binary joins. This supplies the reconstruction map
for both abstract Stonean frames and the opens of their Stone spectra. -/
noncomputable def basisIdealIso (k : B ↪o L) (hbot : k ⊥ = ⊥)
    (hsup : ∀ a b, k (a ⊔ b) = k a ⊔ k b)
    (hcompact : ∀ b, IsCompactElement (k b))
    (hdense : ∀ a : L, a = sSup (k '' {b | k b ≤ a})) : L ≃o Ideal B where
  toFun := basisIdeal k hbot hsup
  invFun I := sSup (k '' (I : Set B))
  left_inv a := (hdense a).symm
  right_inv I := by
    apply SetLike.ext
    intro b
    change k b ≤ sSup (k '' (I : Set B)) ↔ b ∈ I
    constructor
    · intro hb
      have hd : DirectedOn (· ≤ ·) (k '' (I : Set B)) := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hxz, hyz⟩ := I.directed x hx y hy
        exact ⟨k z, ⟨z, hz, rfl⟩, k.monotone hxz, k.monotone hyz⟩
      obtain ⟨_, ⟨c, hc, rfl⟩, hbc⟩ := hcompact b (k '' (I : Set B))
        (sSup (k '' (I : Set B))) (I.nonempty.image k) hd (isLUB_sSup _) hb
      exact I.lower (k.le_iff_le.mp hbc) hc
    · intro hb
      exact le_sSup ⟨b, hb, rfl⟩
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      rw [hdense a]
      apply sSup_le
      rintro _ ⟨x, hx, rfl⟩
      exact h hx
    · intro h x hx
      exact hx.trans h

@[simp] theorem basisIdealIso_apply {k : B ↪o L} {hbot} {hsup} {hcompact} {hdense} (a : L) :
    basisIdealIso k hbot hsup hcompact hdense a = basisIdeal k hbot hsup a := rfl

@[simp] theorem basisIdealIso_symm_apply {k : B ↪o L} {hbot} {hsup} {hcompact} {hdense}
    (I : Ideal B) :
    (basisIdealIso k hbot hsup hcompact hdense).symm I = sSup (k '' (I : Set B)) := rfl

end Gelfand273Ideal

end Gelfand272Component9


section Gelfand272Component10
/- Reused accepted proof by fizzyinc3, submission e4ac8c1d-3289-4144-baeb-8ddb71a3176f. Only a wrapper namespace and theorem name change. -/

namespace Gelfand273Criterion

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_restrict {A : Type u} [CompleteBooleanAlgebra A] (nu : A → ℝ≥0)
    (hnu : IsPositiveContinuousValuation nu) (a : A) :
    IsPositiveContinuousValuation (fun x : Set.Iic a => nu x.val) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu
  refine ⟨⟨hbot, fun x y => hmod x.val y.val⟩, fun x y hxy => hmono hxy, ?_⟩
  intro s b hsne hdir hlub
  have hl : IsLUB (Subtype.val '' s) b.val := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact hlub.1 hx
    · intro u hu
      have : b ≤ ⟨u ⊓ a, inf_le_right⟩ := hlub.2 (fun x hx =>
        show x.val ≤ u ⊓ a from le_inf (hu ⟨x, hx, rfl⟩) x.2)
      exact (show b.val ≤ u ⊓ a from this).trans inf_le_left
  have hd : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z.val, ⟨z, hz, rfl⟩, hxz, hyz⟩
  have h := hcont _ _ (hsne.image _) hd hl
  rw [Set.image_image] at h
  exact h

theorem g67c_extend {A : Type u} [CompleteBooleanAlgebra A] (a : A) (mu : Set.Iic a → ℝ≥0)
    (hmu : IsPositiveContinuousValuation mu) :
    IsPositiveContinuousValuation (fun x : A => mu ⟨x ⊓ a, inf_le_right⟩) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hmu
  refine ⟨⟨?_, fun x y => ?_⟩, fun x y hxy => hmono (show x ⊓ a ≤ y ⊓ a from inf_le_inf_right a hxy), ?_⟩
  · have : (⟨(⊥ : A) ⊓ a, inf_le_right⟩ : Set.Iic a) = ⊥ := Subtype.ext (by simp)
    simp only; rw [this, hbot]
  · have h1 : (⟨(x ⊔ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊔ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊔ y) ⊓ a = (x ⊓ a) ⊔ (y ⊓ a)
        rw [inf_sup_right])
    have h2 : (⟨(x ⊓ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊓ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊓ y) ⊓ a = (x ⊓ a) ⊓ (y ⊓ a)
        rw [inf_inf_distrib_right])
    simp only; rw [h1, h2]; exact hmod _ _
  · intro s b hsne hdir hlub
    let g : A → Set.Iic a := fun x => ⟨x ⊓ a, inf_le_right⟩
    have hb : b = sSup s := hlub.unique (isLUB_sSup s)
    have hl : IsLUB (g '' s) (g b) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact show x ⊓ a ≤ b ⊓ a from inf_le_inf_right a (hlub.1 hx)
      · intro u hu
        show b ⊓ a ≤ u.val
        rw [hb, sSup_inf_eq]
        exact iSup₂_le fun x hx => (show g x ≤ u from hu ⟨x, hx, rfl⟩)
    have hd : DirectedOn (· ≤ ·) (g '' s) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨g z, ⟨z, hz, rfl⟩, show x ⊓ a ≤ z ⊓ a from inf_le_inf_right a hxz,
        show y ⊓ a ≤ z ⊓ a from inf_le_inf_right a hyz⟩
    have h := hcont _ _ (hsne.image _) hd hl
    rw [Set.image_image] at h
    exact h

theorem localizableCriterion (A : Type u) [CompleteBooleanAlgebra A] :
    HasFiniteValuationCover A ↔ ∀ b : A, b ≠ ⊥ →
      ∃ nu : A → ℝ≥0, IsPositiveContinuousValuation nu ∧ nu b ≠ 0 := by
  constructor
  · intro hcov b hb
    have : ∃ g ∈ {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}, b ⊓ g ≠ ⊥ := by
      by_contra hall
      push Not at hall
      apply hb
      have : b = b ⊓ ⊤ := (inf_top_eq b).symm
      rw [this, ← hcov, inf_sSup_eq]
      exact le_antisymm (iSup₂_le fun d hd => (hall d hd).le) bot_le
    obtain ⟨g, ⟨mu, hmu, hfaith⟩, hbg⟩ := this
    refine ⟨_, g67c_extend g mu hmu, fun h0 => hbg ?_⟩
    have := hfaith _ h0
    exact congrArg Subtype.val this
  · intro h
    unfold HasFiniteValuationCover
    set G := {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}
    set g := sSup G
    by_contra hne
    have hgc : gᶜ ≠ ⊥ := fun h' => hne (compl_eq_bot.1 h')
    obtain ⟨nu, hnu, hnz⟩ := h gᶜ hgc
    have hnu' := hnu
    obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu'
    let Z : Set A := {x | nu x = 0}
    set n := sSup Z
    have hsupz : ∀ x y, x ∈ Z → y ∈ Z → x ⊔ y ∈ Z := by
      intro x y hx hy
      have := hmod x y
      simp only [Z, Set.mem_setOf_eq] at hx hy ⊢
      rw [hx, hy, zero_add] at this
      exact (add_eq_zero.1 this.symm).1
    have hn : nu n = 0 := by
      have hc := hcont Z n ⟨⊥, hbot⟩
        (fun x hx y hy => ⟨x ⊔ y, hsupz x y hx hy, le_sup_left, le_sup_right⟩) (isLUB_sSup Z)
      exact le_antisymm (hc.2 (by rintro _ ⟨x, hx, rfl⟩; exact le_of_eq hx)) bot_le
    set c := gᶜ ⊓ nᶜ
    have hcG : c ∈ G := by
      refine ⟨fun x => nu x.val, g67c_restrict nu hnu c, fun x hx => ?_⟩
      apply Subtype.ext
      have hxn : x.val ≤ n := le_sSup hx
      have hxc : x.val ≤ nᶜ := x.2.trans inf_le_right
      show x.val = ⊥
      exact le_antisymm (le_inf hxn hxc |>.trans (inf_compl_self n).le) bot_le
    have hcle : c ≤ g := le_sSup hcG
    have hc0 : c = ⊥ := le_antisymm ((le_inf hcle inf_le_left).trans (inf_compl_self g).le) bot_le
    apply hnz
    have h1 : gᶜ ≤ c ⊔ n := by
      rw [sup_comm, sup_inf_left, sup_compl_eq_top, inf_top_eq]; exact le_sup_right
    have h2 := hmono h1
    rw [hc0, bot_sup_eq, hn] at h2
    exact le_antisymm h2 bot_le

end Gelfand273Criterion
end Gelfand272Component10


section Gelfand272Component11

set_option autoImplicit false

open Set CategoryTheory QAlgorithms.Papers.Independent.Support21.P20
open GelfandVNA.Duality Heyting Gelfand258Work
open scoped NNReal

namespace Gelfand273Work

universe u

/-- The regular elements of a frame form a complete Boolean algebra; joins are
the double negation of the ambient joins (Pavlov, Proposition 2.48). -/
noncomputable instance regularCompleteBooleanAlgebra (L : Type u) [Order.Frame L] :
    CompleteBooleanAlgebra (Heyting.Regular L) where
  __ := (inferInstance : BooleanAlgebra (Heyting.Regular L))
  sSup := (Heyting.Regular.gi (α := L)).liftCompleteLattice.sSup
  sInf := (Heyting.Regular.gi (α := L)).liftCompleteLattice.sInf
  isLUB_sSup := (Heyting.Regular.gi (α := L)).liftCompleteLattice.isLUB_sSup
  isGLB_sInf := (Heyting.Regular.gi (α := L)).liftCompleteLattice.isGLB_sInf

theorem regular_coe_sSup {L : Type u} [Order.Frame L] (s : Set (Heyting.Regular L)) :
    ((sSup s : Heyting.Regular L) : L) = (sSup (((↑) : Heyting.Regular L → L) '' s))ᶜᶜ := rfl

/-- This is the object restriction needed for hyperstonean duality. The two
valuation transports are the already proved positive case of Lemma 2.58. -/
theorem hyperstonean_iff_regular_localizable {L : Type u} [Order.Frame L]
    (hL : IsStoneanLocale L) :
    IsHyperstoneanLocale L ↔ HasFiniteValuationCover (Heyting.Regular L) := by
  rw [Gelfand273Criterion.localizableCriterion]
  constructor
  · intro h b hb
    have hb' : (b : L) ≠ ⊥ := fun e => hb (Heyting.Regular.coe_injective e)
    obtain ⟨ν, hν, hn⟩ := h.2 (b : L) hb'
    exact ⟨fun a : Heyting.Regular L => ν a, restriction_positive_continuous ν hν, hn⟩
  · intro h
    refine ⟨hL, ?_⟩
    intro a ha
    have hqa : Heyting.Regular.toRegular a ≠ (⊥ : Heyting.Regular L) := by
      intro e
      have he : aᶜᶜ = ⊥ := congrArg ((↑) : Heyting.Regular L → L) e
      exact ha (le_antisymm (le_compl_compl.trans he.le) bot_le)
    obtain ⟨μ, hμ, hn⟩ := h (Heyting.Regular.toRegular a) hqa
    exact ⟨fun b => μ (Heyting.Regular.toRegular b), regularize_positive_normal μ hμ, hn⟩

theorem open_map_compl {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) (a : L') :
    f aᶜ = (f a)ᶜ := by
  simpa only [himp_bot, map_bot] using hf.2 a ⊥

theorem open_map_regular {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) {a : L'} (ha : Heyting.IsRegular a) :
    Heyting.IsRegular (f a) := by
  change (f a)ᶜᶜ = f a
  rw [← open_map_compl f hf, ← open_map_compl f hf, ha.eq]

/-- Restriction to regular elements preserves all joins, using preservation of
double negation by an open frame map. -/
noncomputable def regularMap {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) :
    FrameHom (Heyting.Regular L') (Heyting.Regular L) where
  toFun a := ⟨f a, open_map_regular f hf a.prop⟩
  map_top' := Heyting.Regular.coe_injective (map_top f)
  map_inf' a b := Heyting.Regular.coe_injective (map_inf f (a : L') (b : L'))
  map_sSup' s := by
    apply Heyting.Regular.coe_injective
    change f (sSup (((↑) : Heyting.Regular L' → L') '' s))ᶜᶜ =
      (sSup (((↑) : Heyting.Regular L → L) ''
        ((fun a : Heyting.Regular L' => (⟨f a, open_map_regular f hf a.prop⟩ : Heyting.Regular L)) '' s)))ᶜᶜ
    rw [open_map_compl f hf, open_map_compl f hf, map_sSup]
    simp only [Set.image_image, Function.comp_def]
    apply congrArg (fun t : Set L => (sSup t)ᶜᶜ)
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨f a, open_map_regular f hf a.prop⟩, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩

theorem open_map_compact {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (hL : IsStoneanLocale L) (hL' : IsStoneanLocale L')
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) {a : L'} (ha : IsCompactElement a) :
    IsCompactElement (f a) :=
  regular_compact hL (open_map_regular f hf (compact_regular hL' ha))

/-- The measurable locale assigned by the compact-opens construction. -/
noncomputable def cOpenObj (L : HStoneanLoc.{u}) : MLoc.{u} :=
  show MLocObj from
    { carrier := Heyting.Regular L.carrier
      localizable := (hyperstonean_iff_regular_localizable L.hyperstonean.1).mp L.hyperstonean }

/-- The forward functor in Proposition 2.73. -/
noncomputable def cOpenFunctor : HStoneanLoc.{u} ⥤ MLoc.{u} where
  obj := cOpenObj
  map f := InducedCategory.homMk (Frm.ofHom (regularMap f.1 f.2)).op
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def compactOpenIso (L : HStoneanLoc.{u}) :
    (cOpenFunctor.obj L).carrier ≃o {a : L.carrier // IsCompactElement a} :=
  (compactRegularIso L.hyperstonean.1).symm

/-- The compatibility clause of the canonical target holds definitionally for
this forward functor. The equivalence itself is still a separate obligation. -/
theorem compactOpenIso_natural {L L' : HStoneanLoc.{u}} (f : L ⟶ L')
    (b : (cOpenFunctor.obj L').carrier) :
    ((compactOpenIso L (MLoc.frameHom (cOpenFunctor.map f) b) : L.carrier)) =
      f.1 ((compactOpenIso L' b : L'.carrier)) := rfl

end Gelfand273Work

end Gelfand272Component11


section Gelfand272Component12

set_option autoImplicit false
open Set Order Heyting QAlgorithms.Papers.Independent.Support21.P20
open Gelfand258Work

namespace Gelfand273Work
universe u
variable {L : Type u} [Order.Frame L]

theorem compact_sup {a b : L} (ha : IsCompactElement a) (hb : IsCompactElement b) :
    IsCompactElement (a ⊔ b) := by
  intro s u hs hd hlu hab
  obtain ⟨x, hx, hax⟩ := ha s u hs hd hlu (le_sup_left.trans hab)
  obtain ⟨y, hy, hby⟩ := hb s u hs hd hlu (le_sup_right.trans hab)
  obtain ⟨z, hz, hxz, hyz⟩ := hd x hx y hy
  exact ⟨z, hz, sup_le (hax.trans hxz) (hby.trans hyz)⟩

def regularEmbedding : Heyting.Regular L ↪o L where
  toFun a := a
  inj' := Heyting.Regular.coe_injective
  map_rel_iff' := Iff.rfl

theorem regular_coe_sup (hL : IsStoneanLocale L) (a b : Heyting.Regular L) :
    ((a ⊔ b : Heyting.Regular L) : L) = (a : L) ⊔ b :=
  (compact_regular hL (compact_sup (regular_compact hL a.prop)
    (regular_compact hL b.prop))).eq

theorem regular_dense (hL : IsStoneanLocale L) (a : L) :
    a = sSup (regularEmbedding '' {b : Heyting.Regular L | (b : L) ≤ a}) := by
  refine (hL.1.1.2.2 a).trans ?_
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨hx, hxa⟩
    exact ⟨⟨x, compact_regular hL hx⟩, hxa, rfl⟩
  · rintro ⟨b, hba, rfl⟩
    exact ⟨regular_compact hL b.prop, hba⟩

/-- A Stonean frame is recovered from the ideals of its compact opens. -/
noncomputable def regularIdealIso (hL : IsStoneanLocale L) :
    L ≃o Ideal (Heyting.Regular L) :=
  Gelfand273Ideal.basisIdealIso regularEmbedding rfl (regular_coe_sup hL)
    (fun b => regular_compact hL b.prop) (regular_dense hL)

end Gelfand273Work

end Gelfand272Component12


section Gelfand272Component13

set_option autoImplicit false
namespace Gelfand272Spectrum
open TopologicalSpace Heyting Gelfand273Ideal Gelfand273Work
open QAlgorithms.Papers.Independent.Support21.P20
universe u

noncomputable def spectrumIdealIso (B : Type u) [BooleanAlgebra B] :
    Opens (PrimeSpectrum (AsBoolRing B)) ≃o Order.Ideal B :=
  basisIdealIso (basisEmbedding B) (basis_bot B) (basis_sup B)
    (basis_compact B) (basis_density B)

/-- Spatial realization of any canonical Stonean frame, with no point-set
representation assumptions added to the frozen locale predicate. -/
noncomputable def spatialFrameIso {L : Type u} [Order.Frame L] (hL : IsStoneanLocale L) :
    Opens (PrimeSpectrum (AsBoolRing (Heyting.Regular L))) ≃o L :=
  (spectrumIdealIso (Heyting.Regular L)).trans (regularIdealIso hL).symm

end Gelfand272Spectrum
end Gelfand272Component13


section Gelfand272Component14

set_option autoImplicit false
open CategoryTheory TopologicalSpace GelfandVNA.Duality

universe u

namespace Gelfand272Equivalence

def spectrumSpace (A : HStoneanLoc.{u}) : HStonean.{u} where
  toTop := TopCat.of (PrimeSpectrum (AsBoolRing (Heyting.Regular A.carrier)))
  quasiSober := inferInstance
  t0 := inferInstance
  hyperstonean :=
    (Gelfand272Transport.hyperstonean_iff
      (Gelfand272Spectrum.spatialFrameIso A.hyperstonean.1)).mpr A.hyperstonean

def spectrumLocaleIso (A : HStoneanLoc.{u}) : Gelfand272.omega.obj (spectrumSpace A) ≅ A :=
  Gelfand272Transport.localeIso (Gelfand272Spectrum.spatialFrameIso A.hyperstonean.1)

instance omega_essSurj : (Gelfand272.omega.{u}).EssSurj where
  mem_essImage A := ⟨spectrumSpace A, ⟨spectrumLocaleIso A⟩⟩

instance omega_isEquivalence : (Gelfand272.omega.{u}).IsEquivalence where

end Gelfand272Equivalence

open Gelfand272Equivalence

theorem solution :
    ∃ e : HStonean.{u} ≌ HStoneanLoc.{u},
      Nonempty (e.functor ⋙ HStoneanLoc.toLocale ≅ HStonean.toTopFunctor ⋙ topToLocale) := by
  refine ⟨Gelfand272.omega.asEquivalence, ?_⟩
  exact ⟨eqToIso Gelfand272.omega_forget⟩
end Gelfand272Component14


end
