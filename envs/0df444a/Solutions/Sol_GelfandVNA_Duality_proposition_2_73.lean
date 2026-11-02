-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_2_73
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:30:13.207525+00:00
-- url     : https://prove2.me/submissions/96897b1a-221a-4564-9659-f8740cf7a441

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_Locales

/-!
Direct proof of Pavlov's Proposition 2.73, with the canonical definitions.
The valuation helpers are reused from our accepted Lemma 2.58 solution.
The localizability criterion reuses fizzyinc3's accepted proof,
submission e4ac8c1d-3289-4144-baeb-8ddb71a3176f, with a namespace/name wrapper.
All other construction and equivalence proofs are included below.
-/

section Gelfand273_part_ValuationBridge
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
end Gelfand273_part_ValuationBridge

section Gelfand273_part_LocalizableCriterion
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
end Gelfand273_part_LocalizableCriterion

section Gelfand273_part_Forward
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
end Gelfand273_part_Forward

section Gelfand273_part_IdealFrame
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
end Gelfand273_part_IdealFrame

section Gelfand273_part_BasisIso
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
end Gelfand273_part_BasisIso

section Gelfand273_part_IdealStonean
set_option autoImplicit false
open Set Order QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand273Ideal
universe u
variable {A : Type u}

theorem ideal_himp_eq [DistribLattice A] [OrderBot A] (I J : Ideal A) :
    I ⇨ J = idealHimp I J := by
  apply eq_of_forall_le_iff
  intro K
  rw [le_himp_iff, ← idealHimp_gc I K J]
  constructor <;> intro h <;> simpa only [inf_comm] using h

theorem principal_inf [Lattice A] (a b : A) :
    Ideal.principal (a ⊓ b) = Ideal.principal a ⊓ Ideal.principal b := by
  apply SetLike.ext
  intro x
  change (x ≤ a ⊓ b) ↔ (x ≤ a ∧ x ≤ b)
  exact le_inf_iff

theorem principal_sup [SemilatticeSup A] [OrderBot A] (a b : A) :
    Ideal.principal (a ⊔ b) = Ideal.principal a ⊔ Ideal.principal b := by
  ext x
  constructor
  · intro hx
    exact ⟨a, le_rfl, b, le_rfl, hx⟩
  · rintro ⟨y, hy, z, hz, hx⟩
    exact hx.trans (sup_le_sup hy hz)

theorem ideal_coherent [DistribLattice A] [BoundedOrder A] :
    IsCoherentLocale (Ideal A) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Ideal.principal_top] using principal_compact (⊤ : A)
  · intro I J hI hJ
    obtain ⟨a, rfl⟩ := (ideal_compact_iff_principal I).mp hI
    obtain ⟨b, rfl⟩ := (ideal_compact_iff_principal J).mp hJ
    rw [← principal_inf]
    exact principal_compact _
  · intro I
    apply le_antisymm
    · intro a ha
      have hp : Ideal.principal a ≤ sSup {J : Ideal A | IsCompactElement J ∧ J ≤ I} :=
        le_sSup ⟨principal_compact a, Ideal.principal_le_iff.mpr ha⟩
      exact hp Ideal.mem_principal_self
    · exact sSup_le fun J hJ => hJ.2

section CompleteBoolean
variable [CompleteBooleanAlgebra A]

theorem sSup_principal (a : A) : sSup (Ideal.principal a : Set A) = a :=
  le_antisymm (sSup_le fun _ hb => hb) (le_sSup Ideal.mem_principal_self)

/-- In the ideal frame of a complete Boolean algebra, the negation of an ideal
is the principal ideal generated by the complement of its join. -/
theorem ideal_compl (I : Ideal A) :
    Iᶜ = Ideal.principal (sSup (I : Set A))ᶜ := by
  ext x
  rw [← himp_bot, ideal_himp_eq]
  change (∀ a ∈ I, x ⊓ a ∈ (⊥ : Ideal A)) ↔ x ≤ (sSup (I : Set A))ᶜ
  constructor
  · intro h
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    rw [inf_sSup_eq]
    exact iSup₂_le fun a ha => h a ha
  · intro hx a ha
    change x ⊓ a ≤ ⊥
    exact (inf_le_inf_left x (le_sSup ha)).trans
      (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp hx))

theorem ideal_double_compl (I : Ideal A) :
    Iᶜᶜ = Ideal.principal (sSup (I : Set A)) := by
  rw [ideal_compl, ideal_compl, sSup_principal, compl_compl]

theorem ideal_regular : IsRegularLocale (Ideal A) := by
  intro I
  apply le_antisymm
  · intro x hx
    have h : (Ideal.principal x)ᶜ ⊔ I = ⊤ := by
      rw [ideal_compl, sSup_principal]
      apply top_le_iff.mp
      calc
        (⊤ : Ideal A) = Ideal.principal (xᶜ ⊔ x) := by
          rw [compl_sup_eq_top, Ideal.principal_top]
        _ = Ideal.principal xᶜ ⊔ Ideal.principal x := principal_sup _ _
        _ ≤ Ideal.principal xᶜ ⊔ I := sup_le_sup_left (Ideal.principal_le_iff.mpr hx) _
    exact (le_sSup h : Ideal.principal x ≤ sSup {J : Ideal A | Jᶜ ⊔ I = ⊤})
      Ideal.mem_principal_self
  · apply sSup_le
    intro J hJ
    calc
      J = J ⊓ ⊤ := by simp
      _ = J ⊓ (Jᶜ ⊔ I) := congrArg (fun K => J ⊓ K) hJ.symm
      _ = J ⊓ I := by rw [inf_sup_left, inf_compl_eq_bot, bot_sup_eq]
      _ ≤ I := inf_le_right

/-- Ideal completion supplies the Stonean objects in the inverse construction. -/
theorem ideal_stonean : IsStoneanLocale (Ideal A) := by
  refine ⟨⟨ideal_coherent, ideal_regular⟩, ?_⟩
  intro I
  calc
    Iᶜ ⊔ Iᶜᶜ = Ideal.principal (sSup (I : Set A))ᶜ ⊔
        Ideal.principal (sSup (I : Set A)) := congrArg₂ (· ⊔ ·) (ideal_compl I) (ideal_double_compl I)
    _ = Ideal.principal ((sSup (I : Set A))ᶜ ⊔ sSup (I : Set A)) := (principal_sup _ _).symm
    _ = ⊤ := by rw [compl_sup_eq_top, Ideal.principal_top]

end CompleteBoolean
end Gelfand273Ideal
end Gelfand273_part_IdealStonean

section Gelfand273_part_CoherentIso
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
end Gelfand273_part_CoherentIso

section Gelfand273_part_IdealObjects
set_option autoImplicit false
open Set Order CategoryTheory Heyting QAlgorithms.Papers.Independent.Support21.P20
open GelfandVNA.Duality Gelfand258Work

namespace Gelfand273Work
universe u

/-- The original Boolean algebra identifies with the regular elements of its
ideal frame through its principal compact ideals. -/
noncomputable def regularPrincipalIso (A : Type u) [CompleteBooleanAlgebra A] :
    A ≃o Heyting.Regular (Ideal A) :=
  Gelfand273Ideal.principalCompactIso.trans
    (compactRegularIso Gelfand273Ideal.ideal_stonean)

theorem regularIdeal_localizable (A : Type u) [CompleteBooleanAlgebra A]
    (hA : HasFiniteValuationCover A) : HasFiniteValuationCover (Heyting.Regular (Ideal A)) := by
  rw [Gelfand273Criterion.localizableCriterion] at hA ⊢
  intro b hb
  let e := (regularPrincipalIso A).symm
  have heb : e b ≠ ⊥ := by
    intro h
    apply hb
    apply e.injective
    exact h.trans e.map_bot.symm
  obtain ⟨ν, hν, hn⟩ := hA (e b) heb
  exact ⟨ν ∘ e, iso_positive_continuous e ν hν, hn⟩

/-- A localizable Boolean algebra has a hyperstonean ideal frame. -/
noncomputable def idealObj (A : MLoc.{u}) : HStoneanLoc.{u} where
  carrier := Ideal A.carrier
  hyperstonean :=
    (hyperstonean_iff_regular_localizable Gelfand273Ideal.ideal_stonean).mpr
      (regularIdeal_localizable A.carrier A.localizable)

noncomputable def cOpenIdealIso (A : MLoc.{u}) : cOpenFunctor.obj (idealObj A) ≅ A :=
  InducedCategory.isoMk (Frm.Iso.mk (regularPrincipalIso A.carrier)).op

instance cOpenFunctor_essSurj : cOpenFunctor.{u}.EssSurj where
  mem_essImage A := ⟨idealObj A, ⟨cOpenIdealIso A⟩⟩

end Gelfand273Work
end Gelfand273_part_IdealObjects

section Gelfand273_part_IdealMap
set_option autoImplicit false
open Set Order GelfandVNA.Duality

namespace Gelfand273Ideal
universe u
variable {A B : Type u} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra B]

theorem boolean_map_sInf (g : FrameHom A B) (s : Set A) :
    g (sInf s) = sInf (g '' s) := by
  apply compl_injective
  rw [← map_compl' g, compl_sInf', map_sSup, compl_sInf']
  apply congrArg sSup
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro a ha
  exact map_compl' g a

theorem boolean_map_himp (g : FrameHom A B) (a b : A) :
    g (a ⇨ b) = g a ⇨ g b := by
  simp only [BooleanAlgebra.himp_eq, map_sup, map_compl']

/-- The direct image of an ideal under a complete Boolean map. -/
def mapIdeal (g : FrameHom A B) (I : Ideal A) : Ideal B where
  carrier := {b | ∃ a ∈ I, b ≤ g a}
  lower' := by
    rintro x y hxy ⟨a, ha, hya⟩
    exact ⟨a, ha, hxy.trans hya⟩
  nonempty' := ⟨⊥, ⊥, I.bot_mem, bot_le⟩
  directed' := by
    rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩
    refine ⟨x ⊔ y, ⟨a ⊔ b, Ideal.sup_mem ha hb, ?_⟩, le_sup_left, le_sup_right⟩
    rw [map_sup]
    exact sup_le_sup hxa hyb

def comapIdeal (g : FrameHom A B) (J : Ideal B) : Ideal A where
  carrier := {a | g a ∈ J}
  lower' := fun _ _ hxy hy => J.lower (OrderHomClass.monotone g hxy) hy
  nonempty' := ⟨⊥, by change g ⊥ ∈ J; rw [map_bot]; exact J.bot_mem⟩
  directed' := by
    intro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    change g (a ⊔ b) ∈ J
    rw [map_sup]
    exact Ideal.sup_mem ha hb

theorem mapIdeal_gc (g : FrameHom A B) : GaloisConnection (mapIdeal g) (comapIdeal g) := by
  intro I J
  constructor
  · intro h a ha
    exact h ⟨a, ha, le_rfl⟩
  · rintro h b ⟨a, ha, hba⟩
    exact J.lower hba (h ha)

noncomputable def idealMap (g : FrameHom A B) : FrameHom (Ideal A) (Ideal B) where
  toFun := mapIdeal g
  map_top' := by
    apply top_unique
    intro b hb
    exact ⟨⊤, by trivial, by rw [map_top]; exact le_top⟩
  map_inf' I J := by
    apply SetLike.ext
    intro b
    constructor
    · rintro ⟨a, ⟨haI, haJ⟩, hba⟩
      exact ⟨⟨a, haI, hba⟩, ⟨a, haJ, hba⟩⟩
    · rintro ⟨⟨a, ha, hba⟩, ⟨c, hc, hbc⟩⟩
      refine ⟨a ⊓ c, ⟨I.lower inf_le_left ha, J.lower inf_le_right hc⟩, ?_⟩
      rw [map_inf]
      exact le_inf hba hbc
  map_sSup' s := by rw [(mapIdeal_gc g).l_sSup, sSup_image]

noncomputable def lowerAdjoint (g : FrameHom A B) (b : B) : A :=
  sInf {a | b ≤ g a}

theorem lowerAdjoint_unit (g : FrameHom A B) (b : B) : b ≤ g (lowerAdjoint g b) := by
  unfold lowerAdjoint
  rw [boolean_map_sInf]
  apply le_sInf
  rintro _ ⟨a, ha, rfl⟩
  exact ha

theorem lowerAdjoint_gc (g : FrameHom A B) : GaloisConnection (lowerAdjoint g) g := by
  intro b a
  constructor
  · intro h
    exact (lowerAdjoint_unit g b).trans (OrderHomClass.monotone g h)
  · intro h
    exact sInf_le h

theorem mem_mapIdeal_iff (g : FrameHom A B) (I : Ideal A) (b : B) :
    b ∈ mapIdeal g I ↔ lowerAdjoint g b ∈ I := by
  constructor
  · rintro ⟨a, ha, hba⟩
    exact I.lower ((lowerAdjoint_gc g b a).mpr hba) ha
  · intro hb
    exact ⟨lowerAdjoint g b, hb, lowerAdjoint_unit g b⟩

theorem idealMap_isOpen (g : FrameHom A B) : IsOpenFrameHom (idealMap g) := by
  constructor
  · intro s
    change mapIdeal g (sInf s) = sInf (mapIdeal g '' s)
    apply le_antisymm
    · apply le_sInf
      rintro _ ⟨I, hI, rfl⟩
      exact (mapIdeal_gc g).monotone_l (sInf_le hI)
    · intro b hb
      apply (mem_mapIdeal_iff g (sInf s) b).mpr
      apply Ideal.principal_le_iff.mp
      apply le_sInf
      intro I hI
      apply Ideal.principal_le_iff.mpr
      apply (mem_mapIdeal_iff g I b).mp
      exact (sInf_le ⟨I, hI, rfl⟩ : sInf (mapIdeal g '' s) ≤ mapIdeal g I) hb
  · intro I J
    apply SetLike.ext
    intro b
    change b ∈ mapIdeal g (I ⇨ J) ↔ b ∈ (mapIdeal g I ⇨ mapIdeal g J)
    rw [ideal_himp_eq, ideal_himp_eq]
    constructor
    · rintro ⟨a, ha, hba⟩ c ⟨i, hi, hci⟩
      refine ⟨a ⊓ i, ha i hi, ?_⟩
      rw [map_inf]
      exact inf_le_inf hba hci
    · intro h
      refine ⟨lowerAdjoint g b, ?_, lowerAdjoint_unit g b⟩
      intro i hi
      obtain ⟨j, hj, hbj⟩ := h (g i) ⟨i, hi, le_rfl⟩
      apply J.lower ?_ hj
      apply le_himp_iff.mp
      apply (lowerAdjoint_gc g b (i ⇨ j)).mpr
      rw [boolean_map_himp]
      exact le_himp_iff.mpr hbj

@[simp] theorem idealMap_principal (g : FrameHom A B) (a : A) :
    idealMap g (Ideal.principal a) = Ideal.principal (g a) := by
  apply SetLike.ext
  intro b
  constructor
  · rintro ⟨c, hc, hbc⟩
    exact hbc.trans (OrderHomClass.monotone g hc)
  · intro hb
    exact ⟨a, le_rfl, hb⟩

end Gelfand273Ideal
end Gelfand273_part_IdealMap

section Gelfand273_part_Faithful
set_option autoImplicit false

open Set CategoryTheory QAlgorithms.Papers.Independent.Support21.P20
open GelfandVNA.Duality Heyting Gelfand258Work

namespace Gelfand273Work

universe u

/-- Coherence makes restriction to the regular/compact elements faithful. -/
theorem frameHom_eq_of_regular_eq {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (hL' : IsStoneanLocale L') (f g : FrameHom L' L)
    (h : ∀ a : Heyting.Regular L', f (a : L') = g (a : L')) : f = g := by
  ext a
  let s : Set L' := {b | IsCompactElement b ∧ b ≤ a}
  have ha : a = sSup s := hL'.1.1.2.2 a
  have hs : f '' s = g '' s := Set.image_congr (fun b hb => h ⟨b, compact_regular hL' hb.1⟩)
  calc
    f a = f (sSup s) := congrArg f ha
    _ = sSup (f '' s) := map_sSup f s
    _ = sSup (g '' s) := congrArg sSup hs
    _ = g (sSup s) := (map_sSup g s).symm
    _ = g a := congrArg g ha.symm

instance cOpenFunctor_faithful : cOpenFunctor.{u}.Faithful where
  map_injective := by
    intro L L' f g hfg
    apply Subtype.ext
    apply frameHom_eq_of_regular_eq L'.hyperstonean.1
    intro a
    have h := congrArg (fun k => MLoc.frameHom k a) hfg
    exact congrArg ((↑) : Heyting.Regular L.carrier → L.carrier) h

end Gelfand273Work
end Gelfand273_part_Faithful

section Gelfand273_part_Full
set_option autoImplicit false
open Set Order CategoryTheory Heyting GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand273Work
universe u

theorem regularIdealIso_coe {L : Type u} [Order.Frame L]
    (hL : IsStoneanLocale L) (b : Heyting.Regular L) :
    regularIdealIso hL (b : L) = Ideal.principal b := by
  apply SetLike.ext
  intro c
  rfl

theorem regularIdealIso_symm_principal {L : Type u} [Order.Frame L]
    (hL : IsStoneanLocale L) (b : Heyting.Regular L) :
    (regularIdealIso hL).symm (Ideal.principal b) = (b : L) := by
  rw [← regularIdealIso_coe hL b]
  exact (regularIdealIso hL).symm_apply_apply _

theorem orderIso_isOpen {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (e : L' ≃o L) : IsOpenFrameHom (e : FrameHom L' L) :=
  ⟨map_sInf e, map_himp e⟩

/-- Lift a complete Boolean map between compact opens to an open frame map
using the ideal-completion representation of the two frames. -/
noncomputable def liftRegularMap (L L' : HStoneanLoc.{u})
    (g : FrameHom (Heyting.Regular L'.carrier) (Heyting.Regular L.carrier)) :
    FrameHom L'.carrier L.carrier :=
  ((regularIdealIso L.hyperstonean.1).symm : FrameHom _ _).comp
    ((Gelfand273Ideal.idealMap g).comp
      (regularIdealIso L'.hyperstonean.1 : FrameHom _ _))

theorem liftRegularMap_open (L L' : HStoneanLoc.{u})
    (g : FrameHom (Heyting.Regular L'.carrier) (Heyting.Regular L.carrier)) :
    IsOpenFrameHom (liftRegularMap L L' g) :=
  (orderIso_isOpen (regularIdealIso L.hyperstonean.1).symm).comp
    ((Gelfand273Ideal.idealMap_isOpen g).comp
      (orderIso_isOpen (regularIdealIso L'.hyperstonean.1)))

theorem liftRegularMap_coe (L L' : HStoneanLoc.{u})
    (g : FrameHom (Heyting.Regular L'.carrier) (Heyting.Regular L.carrier)) (b : Heyting.Regular L'.carrier) :
    liftRegularMap L L' g (b : L'.carrier) = (g b : L.carrier) := by
  change (regularIdealIso L.hyperstonean.1).symm
    (Gelfand273Ideal.idealMap g (regularIdealIso L'.hyperstonean.1 (b : L'.carrier))) = _
  rw [regularIdealIso_coe, Gelfand273Ideal.idealMap_principal,
    regularIdealIso_symm_principal]

instance cOpenFunctor_full : cOpenFunctor.{u}.Full where
  map_surjective := by
    intro L L' f
    let g := MLoc.frameHom f
    refine ⟨⟨liftRegularMap L L' g, liftRegularMap_open L L' g⟩, ?_⟩
    apply InducedCategory.hom_ext
    apply Quiver.Hom.unop_inj
    apply Frm.hom_ext
    apply FrameHom.ext
    intro b
    apply Heyting.Regular.coe_injective
    exact liftRegularMap_coe L L' g b

end Gelfand273Work
end Gelfand273_part_Full

section Gelfand273_part_Final
open CategoryTheory GelfandVNA.Duality Gelfand273Work
universe u

theorem solution :
    ∃ e : HStoneanLoc.{u} ≌ MLoc.{u},
      ∃ ι : ∀ L : HStoneanLoc.{u}, (e.functor.obj L).carrier ≃o
          {a : L.carrier // IsCompactElement a},
        ∀ {L L' : HStoneanLoc.{u}} (f : L ⟶ L') (b : (e.functor.obj L').carrier),
          ((ι L (MLoc.frameHom (e.functor.map f) b) : L.carrier)) =
            f.1 ((ι L' b : L'.carrier)) := by
  letI : cOpenFunctor.{u}.IsEquivalence := {}
  exact ⟨cOpenFunctor.asEquivalence, compactOpenIso, fun f b => compactOpenIso_natural f b⟩
end Gelfand273_part_Final
