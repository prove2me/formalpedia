-- Prove2me | solution 1 for GelfandVNA.Duality.lemma_2_58
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:49:55.776209+00:00
-- url     : https://prove2.me/submissions/0c29e7e0-bb4f-4fdd-b126-b37d16869627

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Mathlib.Order.Heyting.Regular
import Mathlib.Order.Filter.AtTopBot.Tendsto

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

universe u

theorem solution (L : Type u) [Order.Frame L] (hL : IsStoneanLocale L)
    (B : Type u) [Lattice B] [OrderBot B] (e : B ≃o {a : L // IsCompactElement a}) :
    (∀ ν : L → ℂ, IsNormalValuation ν → IsContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → ℂ, IsContinuousValuation μ →
      ∃! ν : L → ℂ, IsNormalValuation ν ∧ ∀ b, ν (e b) = μ b) ∧
    (∀ ν : L → ℝ, IsNormalValuation ν → IsContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → ℝ, IsContinuousValuation μ →
      ∃! ν : L → ℝ, IsNormalValuation ν ∧ ∀ b, ν (e b) = μ b) ∧
    (∀ ν : L → NNReal, IsPositiveNormalValuation ν →
      IsPositiveContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → NNReal, IsPositiveContinuousValuation μ →
      ∃! ν : L → NNReal, IsPositiveNormalValuation ν ∧ ∀ b, ν (e b) = μ b) := by
  have hc := Gelfand258Work.continuous_extension (R := ℂ) hL e
  have hr := Gelfand258Work.continuous_extension (R := ℝ) hL e
  have hp := Gelfand258Work.positive_extension hL e
  exact ⟨hc.1, hc.2, hr.1, hr.2, hp.1, hp.2⟩
