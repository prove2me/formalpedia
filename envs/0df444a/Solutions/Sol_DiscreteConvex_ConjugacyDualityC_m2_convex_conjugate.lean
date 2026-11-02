-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.m2_convex_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:14:56.684452+00:00
-- url     : https://prove2.me/submissions/9230cb2c-6a46-472d-9d37-dd522e81f588

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegerValuedFn
import Theorems.Thm_DiscreteConvex_ConjugacyDuality_discrete_conjugacy_theorem
import Theorems.Thm_DiscreteConvex_ConjugacyDualityC_l2_convex_biconjugate

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace M2ConjAux

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityC

variable {V : Type*} [Fintype V] [DecidableEq V]

def idot (p x : V → ℤ) : ℤ := ∑ i, p i * x i

lemma dot_eq (p x : V → ℤ) : (∑ i, (p i : ℝ) * (x i : ℝ)) = ((idot p x : ℤ) : ℝ) := by
  simp [idot]

lemma idot_add_right (p x y : V → ℤ) : idot p (x + y) = idot p x + idot p y := by
  simp only [idot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

noncomputable def iv (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : ℤ :=
  if h : ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ) then h.choose else 0

lemma iv_spec {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {x : V → ℤ} (hx : f x ≠ ⊤) :
    f x = (((iv f x : ℤ) : ℝ) : WithTop ℝ) := by
  have h : ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ) := (hZ x).resolve_left hx
  unfold iv
  rw [dif_pos h]
  exact h.choose_spec

lemma iv_of_eq {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {x : V → ℤ} {a : ℝ}
    (h : f x = (a : WithTop ℝ)) : a = ((iv f x : ℤ) : ℝ) := by
  have h2 := iv_spec hZ (x := x) (by rw [h]; exact WithTop.coe_ne_top)
  rw [h] at h2
  exact WithTop.coe_injective h2

lemma fromE_coe (t : ℝ) : FromEReal ((t : ℝ) : EReal) = ((t : ℝ) : WithTop ℝ) := rfl
lemma fromE_top : FromEReal (⊤ : EReal) = ⊤ := rfl
lemma fromE_bot : FromEReal (⊥ : EReal) = ⊤ := rfl
lemma toE_coe (t : ℝ) : ToEReal ((t : ℝ) : WithTop ℝ) = ((t : ℝ) : EReal) := rfl
lemma toE_top : ToEReal (⊤ : WithTop ℝ) = (⊤ : EReal) := rfl

lemma fromE_ge {s : ℝ} {S : EReal} (h : (s : EReal) ≤ S) : ((s : ℝ) : WithTop ℝ) ≤ FromEReal S := by
  induction S using EReal.rec with
  | bot => exact absurd h (by simp)
  | coe t => rw [fromE_coe]; exact WithTop.coe_le_coe.2 (EReal.coe_le_coe_iff.1 h)
  | top => rw [fromE_top]; exact le_top

lemma fromE_le {C : ℝ} {S : EReal} (hb : S ≠ ⊥) (h : S ≤ (C : EReal)) :
    FromEReal S ≤ ((C : ℝ) : WithTop ℝ) := by
  induction S using EReal.rec with
  | bot => exact absurd rfl hb
  | coe t => rw [fromE_coe]; exact WithTop.coe_le_coe.2 (EReal.coe_le_coe_iff.1 h)
  | top => exact absurd h (by simp)

lemma cc_unfold (f : (V → ℤ) → WithTop ℝ) (p : V → ℤ) :
    ConvexConjugate f p = FromEReal (sSup {v : EReal | ∃ x : V → ℤ,
      v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)}) := rfl

lemma term_top {f : (V → ℤ) → WithTop ℝ} {x : V → ℤ} (h : f x = ⊤) (s : ℝ) :
    (s : EReal) - ToEReal (f x) = ⊥ := by
  rw [h, toE_top, EReal.sub_top]

lemma term_val {f : (V → ℤ) → WithTop ℝ} {x : V → ℤ} {a : ℝ} (h : f x = (a : WithTop ℝ)) (s : ℝ) :
    (s : EReal) - ToEReal (f x) = ((s - a : ℝ) : EReal) := by
  rw [h, toE_coe, ← EReal.coe_sub]

lemma cc_ge {f : (V → ℤ) → WithTop ℝ} {x : V → ℤ} {a : ℝ} (h : f x = (a : WithTop ℝ))
    (p : V → ℤ) :
    (((∑ i, (p i : ℝ) * (x i : ℝ)) - a : ℝ) : WithTop ℝ) ≤ ConvexConjugate f p := by
  rw [cc_unfold]
  apply fromE_ge
  apply le_sSup
  exact ⟨x, by rw [term_val h]⟩

lemma cc_le {f : (V → ℤ) → WithTop ℝ} {p : V → ℤ} {C : ℝ} (hne : ∃ x, f x ≠ ⊤)
    (h : ∀ x (a : ℝ), f x = (a : WithTop ℝ) → (∑ i, (p i : ℝ) * (x i : ℝ)) - a ≤ C) :
    ConvexConjugate f p ≤ ((C : ℝ) : WithTop ℝ) := by
  rw [cc_unfold]
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨a0, ha0⟩ := WithTop.ne_top_iff_exists.1 hx0
  apply fromE_le
  · apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot ((∑ i, (p i : ℝ) * (x0 i : ℝ)) - a0))
    apply le_sSup
    exact ⟨x0, by rw [term_val ha0.symm]⟩
  · apply sSup_le
    rintro t ⟨x, rfl⟩
    by_cases hx : f x = ⊤
    · rw [term_top hx]; exact bot_le
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hx
      rw [term_val ha.symm]
      exact EReal.coe_le_coe_iff.2 (h x a ha.symm)

lemma cc_bdd {f : (V → ℤ) → WithTop ℝ} {p : V → ℤ} {c : ℝ}
    (hc : ConvexConjugate f p = ((c : ℝ) : WithTop ℝ)) {x : V → ℤ} {a : ℝ}
    (h : f x = (a : WithTop ℝ)) : (∑ i, (p i : ℝ) * (x i : ℝ)) - a ≤ c := by
  have := cc_ge h p
  rw [hc] at this
  exact WithTop.coe_le_coe.1 this

lemma cc_top_of_unbdd {f : (V → ℤ) → WithTop ℝ} {p : V → ℤ}
    (h : ∀ M : ℝ, ∃ x, ∃ a : ℝ, f x = (a : WithTop ℝ) ∧ M ≤ (∑ i, (p i : ℝ) * (x i : ℝ)) - a) :
    ConvexConjugate f p = ⊤ := by
  by_contra hne
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨x, a, ha, hM⟩ := h (c + 1)
  have := cc_bdd hc.symm ha
  linarith

def IsMaxZ (f : (V → ℤ) → WithTop ℝ) (p x : V → ℤ) : Prop :=
  f x ≠ ⊤ ∧ ∀ y, f y ≠ ⊤ → idot p y - iv f y ≤ idot p x - iv f x

lemma cc_of_max {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {p x : V → ℤ}
    (h : IsMaxZ f p x) :
    ConvexConjugate f p = ((((idot p x - iv f x : ℤ)) : ℝ) : WithTop ℝ) := by
  apply le_antisymm
  · apply cc_le ⟨x, h.1⟩
    intro y a ha
    rw [iv_of_eq hZ ha, dot_eq]
    have := h.2 y (by rw [ha]; exact WithTop.coe_ne_top)
    exact_mod_cast this
  · have := cc_ge (iv_spec hZ h.1) p
    rw [dot_eq] at this
    exact_mod_cast this

lemma cc_ge_Z {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {x : V → ℤ} (hx : f x ≠ ⊤)
    (p : V → ℤ) : ((((idot p x - iv f x : ℤ)) : ℝ) : WithTop ℝ) ≤ ConvexConjugate f p := by
  have := cc_ge (iv_spec hZ hx) p
  rw [dot_eq] at this
  exact_mod_cast this

lemma cc_attain {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {p : V → ℤ}
    (hne : ∃ x, f x ≠ ⊤) (hfin : ConvexConjugate f p ≠ ⊤) : ∃ x, IsMaxZ f p x := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hfin
  have hb : ∃ b : ℤ, ∀ n : ℤ, (∃ y, f y ≠ ⊤ ∧ n = idot p y - iv f y) → n ≤ b := by
    refine ⟨⌊c⌋, ?_⟩
    rintro n ⟨y, hy, rfl⟩
    apply Int.le_floor.2
    have := cc_bdd hc.symm (iv_spec hZ hy)
    rw [dot_eq] at this
    exact_mod_cast this
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨n, ⟨x, hx, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hb ⟨_, x0, hx0, rfl⟩
  exact ⟨x, hx, fun y hy => hmax _ ⟨y, hy, rfl⟩⟩

lemma cc_ne_top_of_bdd {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {p : V → ℤ}
    (hne : ∃ x, f x ≠ ⊤) (B : ℤ) (hB : ∀ y, f y ≠ ⊤ → idot p y - iv f y ≤ B) :
    ConvexConjugate f p ≠ ⊤ := by
  have : ConvexConjugate f p ≤ (((B : ℤ) : ℝ) : WithTop ℝ) := by
    apply cc_le hne
    intro y a ha
    rw [iv_of_eq hZ ha, dot_eq]
    exact_mod_cast hB y (by rw [ha]; exact WithTop.coe_ne_top)
  exact ne_top_of_le_ne_top WithTop.coe_ne_top this

lemma bridge_mnat (f : (V → ℤ) → WithTop ℝ) (h : MNaturalConvex f) :
    DiscreteConvex.MConvexFunctions.MNaturalConvex f := by
  intro x hx y hy u hu
  obtain ⟨v, hv, hineq⟩ := h x hx y hy u (by
    simpa [SuppPos, DiscreteConvex.MConvexFunctions.SuppPos,
      DiscreteConvex.MConvexFunctions.DomZ, DomZ,
      DiscreteConvex.MConvexFunctions.LiftedFunction, LiftedFunction] using hu)
  refine ⟨v, by
    simpa [SuppNeg, DiscreteConvex.MConvexFunctions.SuppNeg] using hv, ?_⟩
  have e1 : ∀ a : Option V, IndicatorVec {a} =
      DiscreteConvex.MConvexFunctions.CharVec a := by
    intro a; funext w
    simp only [IndicatorVec, DiscreteConvex.MConvexFunctions.CharVec]
    split_ifs <;> simp_all
  have eL : DiscreteConvex.MConvexFunctions.LiftedFunction f = LiftedFunction f := rfl
  rw [eL]
  simpa only [e1] using hineq

lemma infconv_attain {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2)
    {x0 : V → ℤ} (hx1 : ConvexConjugate g1 x0 ≠ ⊤) (hx2 : ConvexConjugate g2 x0 ≠ ⊤)
    (h1z : IsIntegerValuedFn (ConvexConjugate g1)) (h2z : IsIntegerValuedFn (ConvexConjugate g2))
    (p : V → ℤ) :
    (∀ p1 p2 : V → ℤ, p = p1 + p2 → InfConv g1 g2 p ≤ g1 p1 + g2 p2) ∧
    (InfConv g1 g2 p ≠ ⊤ → ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ g1 p1 ≠ ⊤ ∧ g2 p2 ≠ ⊤ ∧
      InfConv g1 g2 p = g1 p1 + g2 p2) := by
  set B : ℤ := idot x0 p - iv (ConvexConjugate g1) x0 - iv (ConvexConjugate g2) x0
  have hlow_int : ∀ p1 p2 : V → ℤ, p = p1 + p2 → g1 p1 ≠ ⊤ → g2 p2 ≠ ⊤ →
      B ≤ iv g1 p1 + iv g2 p2 := by
    intro p1 p2 hp hp1 hp2
    have c1 := cc_ge_Z hg1z hp1 x0
    rw [iv_spec h1z hx1] at c1
    have c1' : idot x0 p1 - iv g1 p1 ≤ iv (ConvexConjugate g1) x0 := by exact_mod_cast c1
    have c2 := cc_ge_Z hg2z hp2 x0
    rw [iv_spec h2z hx2] at c2
    have c2' : idot x0 p2 - iv g2 p2 ≤ iv (ConvexConjugate g2) x0 := by exact_mod_cast c2
    have hp' : idot x0 p = idot x0 p1 + idot x0 p2 := by rw [hp, idot_add_right]
    dsimp [B]
    omega
  have hbdd : BddBelow {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2} := by
    refine ⟨(((B : ℤ) : ℝ) : WithTop ℝ), ?_⟩
    rintro L ⟨p1, p2, hp, rfl⟩
    by_cases hp1 : g1 p1 = ⊤
    · rw [hp1, top_add]; exact le_top
    by_cases hp2 : g2 p2 = ⊤
    · rw [hp2, add_top]; exact le_top
    rw [iv_spec hg1z hp1, iv_spec hg2z hp2, ← WithTop.coe_add]
    exact_mod_cast hlow_int p1 p2 hp hp1 hp2
  refine ⟨fun p1 p2 hp => csInf_le hbdd ⟨p1, p2, hp, rfl⟩, ?_⟩
  intro hne
  have hneS : ({L : WithTop ℝ | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2}).Nonempty :=
    ⟨g1 p + g2 0, p, 0, by simp, rfl⟩
  have hnot_all_top : ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ g1 p1 ≠ ⊤ ∧ g2 p2 ≠ ⊤ := by
    by_contra hall
    push Not at hall
    apply hne
    unfold InfConv
    apply le_antisymm le_top
    apply le_csInf hneS
    rintro L ⟨p1, p2, hp, rfl⟩
    by_cases hp1 : g1 p1 = ⊤
    · rw [hp1, top_add]
    · rw [hall p1 p2 hp hp1, add_top]
  obtain ⟨p1_0, p2_0, hp0, hp1_0, hp2_0⟩ := hnot_all_top
  have hbdZ : ∃ b : ℤ, ∀ k : ℤ,
      (∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ g1 p1 ≠ ⊤ ∧ g2 p2 ≠ ⊤ ∧ k = iv g1 p1 + iv g2 p2) →
      b ≤ k := by
    refine ⟨B, ?_⟩
    rintro k ⟨p1, p2, hp, hp1, hp2, rfl⟩
    exact hlow_int p1 p2 hp hp1 hp2
  obtain ⟨k0, ⟨p1, p2, hp, hp1, hp2, rfl⟩, hmin⟩ :=
    Int.exists_least_of_bdd hbdZ ⟨_, p1_0, p2_0, hp0, hp1_0, hp2_0, rfl⟩
  refine ⟨p1, p2, hp, hp1, hp2, ?_⟩
  apply le_antisymm
  · exact csInf_le hbdd ⟨p1, p2, hp, rfl⟩
  · apply le_csInf hneS
    rintro L ⟨q1, q2, hq, rfl⟩
    by_cases hq1 : g1 q1 = ⊤
    · rw [hq1, top_add]; exact le_top
    by_cases hq2 : g2 q2 = ⊤
    · rw [hq2, add_top]; exact le_top
    rw [iv_spec hg1z hp1, iv_spec hg2z hp2, iv_spec hg1z hq1, iv_spec hg2z hq2,
      ← WithTop.coe_add, ← WithTop.coe_add]
    have := hmin (iv g1 q1 + iv g2 q2) ⟨q1, q2, hq, hq1, hq2, rfl⟩
    exact_mod_cast this

lemma cc_infconv {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2)
    (h1z : IsIntegerValuedFn (ConvexConjugate g1)) (h2z : IsIntegerValuedFn (ConvexConjugate g2))
    {x0 : V → ℤ} (hx1 : ConvexConjugate g1 x0 ≠ ⊤) (hx2 : ConvexConjugate g2 x0 ≠ ⊤) :
    ConvexConjugate (InfConv g1 g2) = fun x => ConvexConjugate g1 x + ConvexConjugate g2 x := by
  have hatt := infconv_attain hg1z hg2z hx1 hx2 h1z h2z
  have hicz : IsIntegerValuedFn (InfConv g1 g2) := by
    intro p
    by_cases hp : InfConv g1 g2 p = ⊤
    · exact Or.inl hp
    · obtain ⟨p1, p2, _, hp1, hp2, heq⟩ := (hatt p).2 hp
      right
      refine ⟨iv g1 p1 + iv g2 p2, ?_⟩
      rw [heq, iv_spec hg1z hp1, iv_spec hg2z hp2, ← WithTop.coe_add]
      push_cast; rfl
  have hne1 : ∃ p1, g1 p1 ≠ ⊤ := by
    by_contra h; push Not at h
    apply hx1
    rw [cc_unfold]
    have : sSup {v : EReal | ∃ x : V → ℤ,
        v = ((∑ i, (x0 i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (g1 x)} = ⊥ := by
      apply le_antisymm _ bot_le
      apply sSup_le
      rintro t ⟨x, rfl⟩
      rw [term_top (h x)]
    rw [this, fromE_bot]
  have hne2 : ∃ p2, g2 p2 ≠ ⊤ := by
    by_contra h; push Not at h
    apply hx2
    rw [cc_unfold]
    have : sSup {v : EReal | ∃ x : V → ℤ,
        v = ((∑ i, (x0 i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (g2 x)} = ⊥ := by
      apply le_antisymm _ bot_le
      apply sSup_le
      rintro t ⟨x, rfl⟩
      rw [term_top (h x)]
    rw [this, fromE_bot]
  obtain ⟨p1_0, hp1_0⟩ := hne1
  obtain ⟨p2_0, hp2_0⟩ := hne2
  funext x
  by_cases hfx1 : ConvexConjugate g1 x = ⊤
  · rw [hfx1, top_add]
    apply cc_top_of_unbdd
    intro M
    have hunb : ∃ p1, g1 p1 ≠ ⊤ ∧
        ⌊M⌋ + 1 - (idot x p2_0 - iv g2 p2_0) ≤ idot x p1 - iv g1 p1 := by
      by_contra hb
      push Not at hb
      exact cc_ne_top_of_bdd hg1z ⟨p1_0, hp1_0⟩ (⌊M⌋ + 1 - (idot x p2_0 - iv g2 p2_0))
        (fun p1 hp1 => (hb p1 hp1).le) hfx1
    obtain ⟨p1, hp1, hM1⟩ := hunb
    have hle := (hatt (p1 + p2_0)).1 p1 p2_0 rfl
    have hfin : InfConv g1 g2 (p1 + p2_0) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hp1, hp2_0⟩) hle
    refine ⟨p1 + p2_0, (iv (InfConv g1 g2) (p1 + p2_0) : ℝ), iv_spec hicz hfin, ?_⟩
    rw [dot_eq]
    have hle' : iv (InfConv g1 g2) (p1 + p2_0) ≤ iv g1 p1 + iv g2 p2_0 := by
      rw [iv_spec hicz hfin, iv_spec hg1z hp1, iv_spec hg2z hp2_0, ← WithTop.coe_add] at hle
      exact_mod_cast hle
    have hsum : idot x (p1 + p2_0) = idot x p1 + idot x p2_0 := idot_add_right x p1 p2_0
    have hMfloor : M ≤ (⌊M⌋ : ℝ) + 1 := (Int.lt_floor_add_one M).le
    have hint : ⌊M⌋ + 1 ≤ idot x (p1 + p2_0) - iv (InfConv g1 g2) (p1 + p2_0) := by omega
    have hint' : ((⌊M⌋ + 1 : ℤ) : ℝ) ≤
        ((idot x (p1 + p2_0) - iv (InfConv g1 g2) (p1 + p2_0) : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at hint'
    linarith
  by_cases hfx2 : ConvexConjugate g2 x = ⊤
  · rw [hfx2, add_top]
    apply cc_top_of_unbdd
    intro M
    have hunb : ∃ p2, g2 p2 ≠ ⊤ ∧
        ⌊M⌋ + 1 - (idot x p1_0 - iv g1 p1_0) ≤ idot x p2 - iv g2 p2 := by
      by_contra hb
      push Not at hb
      exact cc_ne_top_of_bdd hg2z ⟨p2_0, hp2_0⟩ (⌊M⌋ + 1 - (idot x p1_0 - iv g1 p1_0))
        (fun p2 hp2 => (hb p2 hp2).le) hfx2
    obtain ⟨p2, hp2, hM2⟩ := hunb
    have hle := (hatt (p1_0 + p2)).1 p1_0 p2 rfl
    have hfin : InfConv g1 g2 (p1_0 + p2) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hp1_0, hp2⟩) hle
    refine ⟨p1_0 + p2, (iv (InfConv g1 g2) (p1_0 + p2) : ℝ), iv_spec hicz hfin, ?_⟩
    rw [dot_eq]
    have hle' : iv (InfConv g1 g2) (p1_0 + p2) ≤ iv g1 p1_0 + iv g2 p2 := by
      rw [iv_spec hicz hfin, iv_spec hg1z hp1_0, iv_spec hg2z hp2, ← WithTop.coe_add] at hle
      exact_mod_cast hle
    have hsum : idot x (p1_0 + p2) = idot x p1_0 + idot x p2 := idot_add_right x p1_0 p2
    have hMfloor : M ≤ (⌊M⌋ : ℝ) + 1 := (Int.lt_floor_add_one M).le
    have hint : ⌊M⌋ + 1 ≤ idot x (p1_0 + p2) - iv (InfConv g1 g2) (p1_0 + p2) := by omega
    have hint' : ((⌊M⌋ + 1 : ℤ) : ℝ) ≤
        ((idot x (p1_0 + p2) - iv (InfConv g1 g2) (p1_0 + p2) : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at hint'
    linarith
  obtain ⟨p1, hp1⟩ := cc_attain hg1z ⟨p1_0, hp1_0⟩ hfx1
  obtain ⟨p2, hp2⟩ := cc_attain hg2z ⟨p2_0, hp2_0⟩ hfx2
  rw [cc_of_max hg1z hp1, cc_of_max hg2z hp2, ← WithTop.coe_add]
  have hle0 := (hatt (p1 + p2)).1 p1 p2 rfl
  have hfin0 : InfConv g1 g2 (p1 + p2) ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hp1.1, hp2.1⟩) hle0
  have hle0' : iv (InfConv g1 g2) (p1 + p2) ≤ iv g1 p1 + iv g2 p2 := by
    rw [iv_spec hicz hfin0, iv_spec hg1z hp1.1, iv_spec hg2z hp2.1, ← WithTop.coe_add] at hle0
    exact_mod_cast hle0
  have hub : ∀ q, InfConv g1 g2 q ≠ ⊤ →
      idot x q - iv (InfConv g1 g2) q ≤ (idot x p1 - iv g1 p1) + (idot x p2 - iv g2 p2) := by
    intro q hq
    obtain ⟨q1, q2, rfl, hq1, hq2, heq⟩ := (hatt q).2 hq
    have heq' : iv (InfConv g1 g2) (q1 + q2) = iv g1 q1 + iv g2 q2 := by
      have h1 := iv_spec hicz hq
      rw [heq, iv_spec hg1z hq1, iv_spec hg2z hq2, ← WithTop.coe_add] at h1
      exact_mod_cast h1.symm
    have h1 := hp1.2 q1 hq1
    have h2 := hp2.2 q2 hq2
    have hsum := idot_add_right x q1 q2
    omega
  have heq0 : idot x (p1 + p2) - iv (InfConv g1 g2) (p1 + p2) =
      (idot x p1 - iv g1 p1) + (idot x p2 - iv g2 p2) := by
    apply le_antisymm (hub (p1 + p2) hfin0)
    have hsum := idot_add_right x p1 p2
    omega
  have hmax : IsMaxZ (InfConv g1 g2) x (p1 + p2) := by
    refine ⟨hfin0, fun q hq => ?_⟩
    rw [heq0]
    exact hub q hq
  rw [cc_of_max hicz hmax, heq0]
  push_cast; rfl

end M2ConjAux

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityC

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MNaturalConvex f1)
    (hf2 : MNaturalConvex f2) (hf1z : IsIntegerValuedFn f1) (hf2z : IsIntegerValuedFn f2)
    (hdom : (DomZ f1 ∩ DomZ f2).Nonempty) :
    ConvexConjugate (fun x => f1 x + f2 x) = InfConv (ConvexConjugate f1) (ConvexConjugate f2) ∧
    ConvexConjugate (ConvexConjugate (fun x => f1 x + f2 x)) = fun x => f1 x + f2 x := by
  have dc := DiscreteConvex.ConjugacyDuality.discrete_conjugacy_theorem (V := V)
  obtain ⟨hg1L, hg1Z, hbg1⟩ := dc.2.2.1 f1 (M2ConjAux.bridge_mnat f1 hf1) hf1z
  obtain ⟨hg2L, hg2Z, hbg2⟩ := dc.2.2.1 f2 (M2ConjAux.bridge_mnat f2 hf2) hf2z
  have hbg1' : ConvexConjugate (ConvexConjugate f1) = f1 := hbg1
  have hbg2' : ConvexConjugate (ConvexConjugate f2) = f2 := hbg2
  obtain ⟨x0, hx01, hx02⟩ := hdom
  have hx1 : ConvexConjugate (ConvexConjugate f1) x0 ≠ ⊤ := by rw [hbg1']; exact hx01
  have hx2 : ConvexConjugate (ConvexConjugate f2) x0 ≠ ⊤ := by rw [hbg2']; exact hx02
  have h1z : IsIntegerValuedFn (ConvexConjugate (ConvexConjugate f1)) := by rw [hbg1']; exact hf1z
  have h2z : IsIntegerValuedFn (ConvexConjugate (ConvexConjugate f2)) := by rw [hbg2']; exact hf2z
  have hcc := M2ConjAux.cc_infconv (g1 := ConvexConjugate f1) (g2 := ConvexConjugate f2)
    hg1Z hg2Z h1z h2z hx1 hx2
  rw [hbg1', hbg2'] at hcc
  have hbic := l2_convex_biconjugate (ConvexConjugate f1) (ConvexConjugate f2) hg1L hg2L hg1Z hg2Z
  refine ⟨?_, ?_⟩
  · rw [← hcc, hbic]
  · rw [← hcc, hbic, hcc]
