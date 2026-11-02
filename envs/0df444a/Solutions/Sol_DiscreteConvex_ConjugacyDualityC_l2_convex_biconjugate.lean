-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.l2_convex_biconjugate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:31:44.769432+00:00
-- url     : https://prove2.me/submissions/764f5484-f747-4b30-8765-d625f4d62408

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegerValuedFn
import Theorems.Thm_DiscreteConvex_MConvexSets_discrete_separation_submodular
import Theorems.Thm_DiscreteConvex_LConvexSets_discrete_separation_lconvex

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace L2BicAux

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityC

section A
variable {V : Type*} [Fintype V] [DecidableEq V]

def idot (p x : V → ℤ) : ℤ := ∑ i, p i * x i

lemma dot_eq (p x : V → ℤ) : (∑ i, (p i : ℝ) * (x i : ℝ)) = ((idot p x : ℤ) : ℝ) := by
  simp [idot]

lemma idot_comm (p x : V → ℤ) : idot p x = idot x p := by
  simp only [idot, mul_comm]

lemma idot_add_left (p q x : V → ℤ) : idot (p + q) x = idot p x + idot q x := by
  simp only [idot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma idot_add_right (p x y : V → ℤ) : idot p (x + y) = idot p x + idot p y := by
  simp only [idot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma idot_smul_left (t : ℤ) (q x : V → ℤ) : idot (t • q) x = t * idot q x := by
  simp only [idot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma idot_one_right (p : V → ℤ) : idot p (1 : V → ℤ) = ∑ i, p i := by
  simp [idot]

lemma idot_sup_inf (z a b : V → ℤ) : idot z (a ⊔ b) + idot z (a ⊓ b) = idot z a + idot z b := by
  simp only [idot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (a ⊔ b) i + (a ⊓ b) i = a i + b i := by
    show max (a i) (b i) + min (a i) (b i) = a i + b i
    omega
  linarith [congrArg (z i * ·) this]

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

lemma cc_empty {f : (V → ℤ) → WithTop ℝ} (h : ∀ x, f x = ⊤) (p : V → ℤ) :
    ConvexConjugate f p = ⊤ := by
  rw [cc_unfold]
  have : sSup {v : EReal | ∃ x : V → ℤ,
      v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)} = ⊥ := by
    apply le_antisymm _ bot_le
    apply sSup_le
    rintro t ⟨x, rfl⟩
    rw [term_top (h x)]
  rw [this, fromE_bot]

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

lemma cc_ne_top_of_bdd {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {p : V → ℤ}
    (hne : ∃ x, f x ≠ ⊤) (B : ℤ) (hB : ∀ y, f y ≠ ⊤ → idot p y - iv f y ≤ B) :
    ConvexConjugate f p ≠ ⊤ := by
  have : ConvexConjugate f p ≤ (((B : ℤ) : ℝ) : WithTop ℝ) := by
    apply cc_le hne
    intro y a ha
    rw [iv_of_eq hZ ha, dot_eq]
    exact_mod_cast hB y (by rw [ha]; exact WithTop.coe_ne_top)
  exact ne_top_of_le_ne_top WithTop.coe_ne_top this

lemma biconj_of_max {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {x p : V → ℤ}
    (hp : IsMaxZ f p x) : ConvexConjugate (ConvexConjugate f) x = f x := by
  have hfx := iv_spec hZ hp.1
  rw [hfx]
  have hcp := cc_of_max hZ hp
  apply le_antisymm
  · apply cc_le ⟨p, by rw [hcp]; exact WithTop.coe_ne_top⟩
    intro q a ha
    have := cc_ge hfx q
    rw [ha, WithTop.coe_le_coe] at this
    have e : (∑ i, (x i : ℝ) * (q i : ℝ)) = ∑ i, (q i : ℝ) * (x i : ℝ) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]; linarith
  · have h := cc_ge hcp x
    rw [dot_eq, idot_comm] at h
    convert h using 2
    push_cast; ring

end A

section LocGlob

theorem loc_glob {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : (W → ℤ) → WithTop ℝ)
    (hsub : ∀ p q, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q)
    (htr : ∀ p, G (p + 1) = G p) (z : W → ℤ) (hz : G z ≠ ⊤)
    (hloc : ∀ X : Finset W, G z ≤ G (fun a => z a + if a ∈ X then 1 else 0)) :
    ∀ y, G z ≤ G y := by
  have htrk : ∀ (k : ℕ) (p : W → ℤ), G (fun a => p a + k) = G p := by
    intro k
    induction k with
    | zero => intro p; simp
    | succ k ih =>
      intro p
      rw [← ih p, ← htr (fun a => p a + k)]
      congr 1; funext a; simp; ring
  have key : ∀ M : ℕ, ∀ y : W → ℤ, (∀ a, z a ≤ y a) → (∀ a, y a - z a ≤ M) → G z ≤ G y := by
    intro M
    induction M with
    | zero =>
      intro y h1 h2
      have : y = z := funext fun a => by have := h1 a; have := h2 a; push_cast at *; omega
      rw [this]
    | succ M ih =>
      intro y h1 h2
      set U := Finset.univ.filter (fun a => z a < y a) with hU
      set y' : W → ℤ := (y - 1) ⊔ z with hy'
      have hs := hsub (y - 1) z
      have e1 : G (y - 1) = G y := by
        have := htr (y - 1); rw [sub_add_cancel] at this; exact this.symm
      have e2 : G ((y - 1) ⊓ z) = G (fun a => z a + if a ∈ U then 1 else 0) := by
        rw [← htr]; congr 1; funext a
        simp only [Pi.add_apply, Pi.inf_apply, Pi.sub_apply, Pi.one_apply, hU,
          Finset.mem_filter, Finset.mem_univ, true_and]
        have := h1 a
        split_ifs with h <;> omega
      have hy'1 : G z ≤ G y' := by
        apply ih y'
        · intro a; simp only [hy', Pi.sup_apply]; omega
        · intro a; simp only [hy', Pi.sup_apply, Pi.sub_apply, Pi.one_apply]
          have := h1 a; have := h2 a; push_cast at *; omega
      have hl := hloc U
      have hle : G y' + G z ≤ G y + G z := by
        calc G y' + G z ≤ G y' + G ((y - 1) ⊓ z) := by rw [e2]; exact add_le_add le_rfl hl
          _ ≤ G (y - 1) + G z := hs
          _ = G y + G z := by rw [e1]
      have := (WithTop.add_le_add_iff_right hz).mp hle
      exact le_trans hy'1 this
  intro y
  obtain ⟨a0, -, ha0⟩ := Finset.exists_min_image Finset.univ (fun a => y a - z a)
    Finset.univ_nonempty
  set y0 : W → ℤ := fun a => y a - (y a0 - z a0) with hy0
  obtain ⟨b0, -, hb0⟩ := Finset.exists_max_image Finset.univ (fun a => y0 a - z a)
    Finset.univ_nonempty
  have hge : ∀ a, z a ≤ y0 a := by
    intro a; have := ha0 a (Finset.mem_univ a); simp only [hy0]; omega
  have hyy : G y = G y0 := by
    rcases le_total 0 (y a0 - z a0) with h | h
    · have := htrk (y a0 - z a0).toNat y0
      rw [← this]; congr 1; funext a; simp only [hy0]; omega
    · have := htrk (z a0 - y a0).toNat y
      rw [← this]; congr 1; funext a; simp only [hy0]; omega
  rw [hyy]
  apply key (y0 b0 - z b0).toNat y0 hge
  intro a
  have := hb0 a (Finset.mem_univ a)
  have := hge b0
  omega

noncomputable def chi {W : Type*} (X : Finset W) : W → ℤ := fun a => if a ∈ X then 1 else 0

lemma idot_chi {W : Type*} [Fintype W] (z : W → ℤ) (X : Finset W) :
    idot z (chi X) = ∑ a ∈ X, z a := by
  simp [idot, chi, Finset.sum_ite_mem, Finset.univ_inter]

lemma lmax_of_local0 {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {g : (W → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValuedFn g)
    (htr : ∀ p, g (p + 1) = g p) {z p : W → ℤ}
    (hsz : ∑ i, z i = 0) (hp : g p ≠ ⊤)
    (hloc : ∀ X : Finset W, g (p + chi X) ≠ ⊤ →
      ∑ a ∈ X, z a ≤ iv g (p + chi X) - iv g p) : IsMaxZ g z p := by
  refine ⟨hp, fun q hq => ?_⟩
  let G : (W → ℤ) → WithTop ℝ := fun q => g q + ((((-(idot z q)) : ℤ) : ℝ) : WithTop ℝ)
  have hsub : ∀ a b, G (a ⊔ b) + G (a ⊓ b) ≤ G a + G b := by
    intro a b
    simp only [G]
    rw [add_add_add_comm, add_add_add_comm (g a), ← WithTop.coe_add, ← WithTop.coe_add]
    have e := idot_sup_inf z a b
    have e2 : ((-(idot z (a ⊔ b)) : ℤ) : ℝ) + ((-(idot z (a ⊓ b)) : ℤ) : ℝ) =
        ((-(idot z a) : ℤ) : ℝ) + ((-(idot z b) : ℤ) : ℝ) := by
      push_cast
      have e' : ((idot z (a ⊔ b) : ℤ) : ℝ) + ((idot z (a ⊓ b) : ℤ) : ℝ) =
          ((idot z a : ℤ) : ℝ) + ((idot z b : ℤ) : ℝ) := by exact_mod_cast e
      linarith
    rw [e2]
    exact add_le_add (hs a b) le_rfl
  have hGtr : ∀ a, G (a + 1) = G a := by
    intro a
    simp only [G]
    rw [htr, idot_add_right, idot_one_right, hsz, add_zero]
  have hGp : G p ≠ ⊤ := WithTop.add_ne_top.2 ⟨hp, WithTop.coe_ne_top⟩
  have hl : ∀ X : Finset W, G p ≤ G (fun a => p a + if a ∈ X then 1 else 0) := by
    intro X
    have e : (fun a => p a + if a ∈ X then (1 : ℤ) else 0) = p + chi X := by
      funext a; simp [chi]
    rw [e]
    by_cases hX : g (p + chi X) = ⊤
    · simp only [G, hX, top_add]; exact le_top
    · have h1 := hloc X hX
      simp only [G]
      rw [iv_spec hZ hX, iv_spec hZ hp, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe,
        idot_add_right, idot_chi]
      have h2 : iv g p - idot z p ≤ iv g (p + chi X) - (idot z p + ∑ a ∈ X, z a) := by omega
      have h3 : ((iv g p - idot z p : ℤ) : ℝ) ≤
          ((iv g (p + chi X) - (idot z p + ∑ a ∈ X, z a) : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at h3 ⊢; linarith
  have hglob := loc_glob G hsub hGtr p hGp hl q
  simp only [G] at hglob
  rw [iv_spec hZ hq, iv_spec hZ hp, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hglob
  have h4 : ((iv g p - idot z p : ℤ) : ℝ) ≤ ((iv g q - idot z q : ℤ) : ℝ) := by
    push_cast at hglob ⊢; linarith
  have h5 : iv g p - idot z p ≤ iv g q - idot z q := by exact_mod_cast h4
  omega

end LocGlob

section LiftSubgrad
variable {V : Type*} [Fintype V] [DecidableEq V]

def liftZ (p : V → ℤ) : Option V → ℤ := fun o => Option.elim o 0 p

lemma lift_eval (g : (V → ℤ) → WithTop ℝ) (p : V → ℤ) :
    LiftedFunctionL g (liftZ p) = g p := by
  simp [LiftedFunctionL, liftZ]

lemma lift_tr (g : (V → ℤ) → WithTop ℝ) (W : Option V → ℤ) :
    LiftedFunctionL g (W + 1) = LiftedFunctionL g W := by
  simp only [LiftedFunctionL, Pi.add_apply, Pi.one_apply]
  congr 1; funext v; ring

lemma lift_intval {g : (V → ℤ) → WithTop ℝ} (hg : IsIntegerValuedFn g) :
    IsIntegerValuedFn (LiftedFunctionL g) :=
  fun W => hg (fun v => W (some v) - W none)

lemma iv_congr {W1 W2 : Type*} {f : (W1 → ℤ) → WithTop ℝ} {g : (W2 → ℤ) → WithTop ℝ}
    {x : W1 → ℤ} {y : W2 → ℤ} (h : f x = g y) : iv f x = iv g y := by
  unfold iv; simp only [h]

lemma idot_lift {y : Option V → ℤ} (_hy : ∑ o : Option V, y o = 0) (p : V → ℤ) :
    idot y (liftZ p) = idot (fun v => y (some v)) p := by
  simp [idot, liftZ, Fintype.sum_option]

lemma chi_sup {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z + chi X) ⊔ (Z + chi Y) = Z + chi (X ∪ Y) := by
  funext a
  show max ((Z + chi X) a) ((Z + chi Y) a) = (Z + chi (X ∪ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

lemma chi_inf {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z + chi X) ⊓ (Z + chi Y) = Z + chi (X ∩ Y) := by
  funext a
  show min ((Z + chi X) a) ((Z + chi Y) a) = (Z + chi (X ∩ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

lemma sub_chi_sup {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z - chi X) ⊔ (Z - chi Y) = Z - chi (X ∩ Y) := by
  funext a
  show max ((Z - chi X) a) ((Z - chi Y) a) = (Z - chi (X ∩ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

lemma sub_chi_inf {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z - chi X) ⊓ (Z - chi Y) = Z - chi (X ∪ Y) := by
  funext a
  show min ((Z - chi X) a) ((Z - chi Y) a) = (Z - chi (X ∪ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

theorem subgrad_at_min {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1 : LNaturalConvex g1) (hg2 : LNaturalConvex g2)
    (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2)
    {p0 p1s p2s : V → ℤ} (hp0 : p0 = p1s + p2s)
    (hp1 : g1 p1s ≠ ⊤) (hp2 : g2 p2s ≠ ⊤)
    (hmin : ∀ p1 p2 : V → ℤ, p0 = p1 + p2 → g1 p1 ≠ ⊤ → g2 p2 ≠ ⊤ →
      iv g1 p1s + iv g2 p2s ≤ iv g1 p1 + iv g2 p2) :
    ∃ x : V → ℤ, IsMaxZ g1 x p1s ∧ IsMaxZ g2 x p2s := by
  let G1 := LiftedFunctionL g1
  let G2 := LiftedFunctionL g2
  have hs1 : SBF G1 := hg1.1
  have hs2 : SBF G2 := hg2.1
  have hG1Z : IsIntegerValuedFn G1 := lift_intval hg1z
  have hG2Z : IsIntegerValuedFn G2 := lift_intval hg2z
  let Z1 := liftZ p1s
  let Z2 := liftZ p2s
  have hZ1 : G1 Z1 ≠ ⊤ := by change LiftedFunctionL g1 (liftZ p1s) ≠ ⊤; rw [lift_eval]; exact hp1
  have hZ2 : G2 Z2 ≠ ⊤ := by change LiftedFunctionL g2 (liftZ p2s) ≠ ⊤; rw [lift_eval]; exact hp2
  have hivZ1 : iv G1 Z1 = iv g1 p1s := iv_congr (lift_eval g1 p1s)
  have hivZ2 : iv G2 Z2 = iv g2 p2s := iv_congr (lift_eval g2 p2s)
  let ρ : Finset (Option V) → WithTop ℝ := fun Y =>
    if G1 (Z1 + chi Y) = ⊤ then ⊤ else (((iv G1 (Z1 + chi Y) - iv G1 Z1 : ℤ) : ℝ) : WithTop ℝ)
  let μ : Finset (Option V) → WithBot ℝ := fun Y =>
    if G2 (Z2 - chi Y) = ⊤ then ⊥ else (((iv G2 Z2 - iv G2 (Z2 - chi Y) : ℤ) : ℝ) : WithBot ℝ)
  have hchi0 : chi (∅ : Finset (Option V)) = 0 := by funext o; simp [chi]
  have hchiu : chi (Finset.univ : Finset (Option V)) = 1 := by funext o; simp [chi]
  have hZ1u : G1 (Z1 + 1) = G1 Z1 := lift_tr g1 Z1
  have hZ2u : G2 (Z2 - 1) = G2 Z2 := by
    have := lift_tr g2 (Z2 - 1)
    rw [sub_add_cancel] at this
    exact this.symm
  have hρ0 : ρ ∅ = 0 := by simp [ρ, hchi0, hZ1]
  have hρu : ρ Finset.univ = 0 := by
    have h1 : G1 (Z1 + chi Finset.univ) = G1 Z1 := by rw [hchiu, hZ1u]
    simp [ρ, h1, hZ1, iv_congr h1]
  have hμ0 : μ ∅ = 0 := by simp [μ, hchi0, hZ2]
  have hμu : μ Finset.univ = 0 := by
    have h1 : G2 (Z2 - chi Finset.univ) = G2 Z2 := by rw [hchiu, hZ2u]
    simp [μ, h1, hZ2, iv_congr h1]
  have hρ_sub : DiscreteConvex.MConvexSets.SubmodularSetFunction ρ := by
    refine ⟨hρ0, by rw [hρu]; exact WithTop.coe_ne_top, fun X Y => ?_⟩
    by_cases hX : G1 (Z1 + chi X) = ⊤
    · simp [ρ, hX]
    by_cases hY : G1 (Z1 + chi Y) = ⊤
    · simp [ρ, hY]
    have hs := hs1 (Z1 + chi X) (Z1 + chi Y)
    rw [chi_sup, chi_inf] at hs
    have hfin : G1 (Z1 + chi (X ∪ Y)) + G1 (Z1 + chi (X ∩ Y)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hX, hY⟩) hs
    obtain ⟨hU, hI⟩ := WithTop.add_ne_top.1 hfin
    rw [iv_spec hG1Z hU, iv_spec hG1Z hI, iv_spec hG1Z hX, iv_spec hG1Z hY,
      ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hs
    have hs' : iv G1 (Z1 + chi (X ∪ Y)) + iv G1 (Z1 + chi (X ∩ Y)) ≤
        iv G1 (Z1 + chi X) + iv G1 (Z1 + chi Y) := by exact_mod_cast hs
    simp only [ρ, if_neg hX, if_neg hY, if_neg hU, if_neg hI, ge_iff_le,
      ← WithTop.coe_add, WithTop.coe_le_coe]
    have : ((iv G1 (Z1 + chi (X ∪ Y)) - iv G1 Z1 + (iv G1 (Z1 + chi (X ∩ Y)) - iv G1 Z1) : ℤ) : ℝ) ≤
        ((iv G1 (Z1 + chi X) - iv G1 Z1 + (iv G1 (Z1 + chi Y) - iv G1 Z1) : ℤ) : ℝ) := by
      exact_mod_cast (by omega)
    push_cast at this ⊢; linarith
  have hμ_sup : DiscreteConvex.MConvexSets.SupermodularSetFunction μ := by
    refine ⟨hμ0, by rw [hμu]; exact WithBot.coe_ne_bot, fun X Y => ?_⟩
    by_cases hX : G2 (Z2 - chi X) = ⊤
    · simp [μ, hX]
    by_cases hY : G2 (Z2 - chi Y) = ⊤
    · simp [μ, hY]
    have hs := hs2 (Z2 - chi X) (Z2 - chi Y)
    rw [sub_chi_sup, sub_chi_inf] at hs
    have hfin : G2 (Z2 - chi (X ∩ Y)) + G2 (Z2 - chi (X ∪ Y)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hX, hY⟩) hs
    obtain ⟨hI, hU⟩ := WithTop.add_ne_top.1 hfin
    rw [iv_spec hG2Z hI, iv_spec hG2Z hU, iv_spec hG2Z hX, iv_spec hG2Z hY,
      ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hs
    have hs' : iv G2 (Z2 - chi (X ∩ Y)) + iv G2 (Z2 - chi (X ∪ Y)) ≤
        iv G2 (Z2 - chi X) + iv G2 (Z2 - chi Y) := by exact_mod_cast hs
    simp only [μ, if_neg hX, if_neg hY, if_neg hU, if_neg hI,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    have : ((iv G2 Z2 - iv G2 (Z2 - chi X) + (iv G2 Z2 - iv G2 (Z2 - chi Y)) : ℤ) : ℝ) ≤
        ((iv G2 Z2 - iv G2 (Z2 - chi (X ∪ Y)) + (iv G2 Z2 - iv G2 (Z2 - chi (X ∩ Y))) : ℤ) : ℝ) := by
      exact_mod_cast (by omega)
    push_cast at this ⊢; linarith
  have hsep : ∀ Y : Finset (Option V),
      DiscreteConvex.MConvexSets.ToERealOfBot (μ Y) ≤ DiscreteConvex.MConvexSets.ToEReal (ρ Y) := by
    intro Y
    by_cases h1 : G1 (Z1 + chi Y) = ⊤
    · simp only [ρ, if_pos h1, DiscreteConvex.MConvexSets.ToEReal]; exact le_top
    by_cases h2 : G2 (Z2 - chi Y) = ⊤
    · simp only [μ, if_pos h2, DiscreteConvex.MConvexSets.ToERealOfBot]; exact bot_le
    simp only [ρ, μ, if_neg h1, if_neg h2]
    change (((iv G2 Z2 - iv G2 (Z2 - chi Y) : ℤ) : ℝ) : EReal) ≤
      (((iv G1 (Z1 + chi Y) - iv G1 Z1 : ℤ) : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff]
    let q1 : V → ℤ := fun v => (Z1 + chi Y) (some v) - (Z1 + chi Y) none
    let q2 : V → ℤ := fun v => (Z2 - chi Y) (some v) - (Z2 - chi Y) none
    have hq0 : p0 = q1 + q2 := by
      funext v
      have := congrFun hp0 v
      simp only [q1, q2, Z1, Z2, liftZ, Pi.add_apply, Pi.sub_apply, Option.elim] at this ⊢
      omega
    have hq1 : g1 q1 = G1 (Z1 + chi Y) := rfl
    have hq2 : g2 q2 = G2 (Z2 - chi Y) := rfl
    have hm := hmin q1 q2 hq0 (by rwa [hq1]) (by rwa [hq2])
    have e1 : iv G1 (Z1 + chi Y) = iv g1 q1 := rfl
    have e2 : iv G2 (Z2 - chi Y) = iv g2 q2 := rfl
    rw [hivZ1, hivZ2, e1, e2]
    exact_mod_cast (by omega : iv g2 p2s - iv g2 q2 ≤ iv g1 q1 - iv g1 p1s)
  have hρZ : DiscreteConvex.MConvexSets.IsIntegerValued ρ := by
    intro Y
    by_cases h : G1 (Z1 + chi Y) = ⊤
    · exact Or.inl (by simp [ρ, h])
    · exact Or.inr ⟨iv G1 (Z1 + chi Y) - iv G1 Z1, by simp [ρ, h]⟩
  have hμZ : DiscreteConvex.MConvexSets.IsIntegerValuedBot μ := by
    intro Y
    by_cases h : G2 (Z2 - chi Y) = ⊤
    · exact Or.inl (by simp [μ, h])
    · exact Or.inr ⟨iv G2 Z2 - iv G2 (Z2 - chi Y), by simp [μ, h]⟩
  obtain ⟨y, hy⟩ :=
    (DiscreteConvex.MConvexSets.discrete_separation_submodular ρ μ hρ_sub hμ_sup hsep).2 hρZ hμZ
  have hy_ρ : ∀ Y : Finset (Option V), G1 (Z1 + chi Y) ≠ ⊤ →
      ∑ o ∈ Y, y o ≤ iv G1 (Z1 + chi Y) - iv G1 Z1 := by
    intro Y hY
    have h := (hy Y).2
    simp only [ρ, if_neg hY] at h
    change (((∑ o ∈ Y, (y o : ℝ) : ℝ)) : EReal) ≤
      (((iv G1 (Z1 + chi Y) - iv G1 Z1 : ℤ) : ℝ) : EReal) at h
    rw [EReal.coe_le_coe_iff] at h
    exact_mod_cast h
  have hy_μ : ∀ Y : Finset (Option V), G2 (Z2 - chi Y) ≠ ⊤ →
      iv G2 Z2 - iv G2 (Z2 - chi Y) ≤ ∑ o ∈ Y, y o := by
    intro Y hY
    have h := (hy Y).1
    simp only [μ, if_neg hY] at h
    change (((iv G2 Z2 - iv G2 (Z2 - chi Y) : ℤ) : ℝ) : EReal) ≤
      (((∑ o ∈ Y, (y o : ℝ) : ℝ)) : EReal) at h
    rw [EReal.coe_le_coe_iff] at h
    exact_mod_cast h
  have hsum_y : ∑ o : Option V, y o = 0 := by
    have h1 := hy_ρ Finset.univ (by rw [hchiu, hZ1u]; exact hZ1)
    have h2 := hy_μ Finset.univ (by rw [hchiu, hZ2u]; exact hZ2)
    have e1 : iv G1 (Z1 + chi Finset.univ) = iv G1 Z1 := iv_congr (by rw [hchiu, hZ1u])
    have e2 : iv G2 (Z2 - chi Finset.univ) = iv G2 Z2 := iv_congr (by rw [hchiu, hZ2u])
    rw [e1, sub_self] at h1
    rw [e2, sub_self] at h2
    omega
  have hmax1 : IsMaxZ G1 y Z1 :=
    lmax_of_local0 hs1 hG1Z (lift_tr g1) hsum_y hZ1 hy_ρ
  let U : (Option V → ℤ) → WithTop ℝ := fun W => G2 (-W)
  have hU_sbf : SBF U := by
    intro a b
    show G2 (-(a ⊔ b)) + G2 (-(a ⊓ b)) ≤ G2 (-a) + G2 (-b)
    rw [neg_sup, neg_inf, add_comm (G2 (-a ⊓ -b))]
    exact hs2 (-a) (-b)
  have hU_Z : IsIntegerValuedFn U := fun W => hG2Z (-W)
  have hU_tr : ∀ W, U (W + 1) = U W := by
    intro W
    show G2 (-(W + 1)) = G2 (-W)
    have e : -W = -(W + 1) + 1 := by funext o; simp
    rw [e]; exact (lift_tr g2 (-(W + 1))).symm
  have hUZ2 : U (-Z2) ≠ ⊤ := by show G2 (- -Z2) ≠ ⊤; rw [neg_neg]; exact hZ2
  have hivU : ∀ W, iv U W = iv G2 (-W) := fun _ => rfl
  have hmaxU : IsMaxZ U (-y) (-Z2) := by
    apply lmax_of_local0 hU_sbf hU_Z hU_tr (by simp [Finset.sum_neg_distrib, hsum_y]) hUZ2
    intro Y hY
    have hY' : G2 (Z2 - chi Y) ≠ ⊤ := by
      convert hY using 2; funext o; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring
    have hm := hy_μ Y hY'
    have e : iv U (-Z2 + chi Y) = iv G2 (Z2 - chi Y) := by
      show iv G2 (-(-Z2 + chi Y)) = iv G2 (Z2 - chi Y)
      congr 1; funext o; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring
    have e0 : iv U (-Z2) = iv G2 Z2 := by show iv G2 (- -Z2) = iv G2 Z2; rw [neg_neg]
    simp only [Pi.neg_apply, Finset.sum_neg_distrib, e, e0]
    omega
  refine ⟨fun v => y (some v), ⟨hp1, fun q hq => ?_⟩, ⟨hp2, fun q hq => ?_⟩⟩
  · have hq' : G1 (liftZ q) ≠ ⊤ := by change LiftedFunctionL g1 (liftZ q) ≠ ⊤; rw [lift_eval]; exact hq
    have h := hmax1.2 (liftZ q) hq'
    have eq1 : iv G1 (liftZ q) = iv g1 q := iv_congr (lift_eval g1 q)
    rw [idot_lift hsum_y q, idot_lift hsum_y p1s, eq1, hivZ1] at h
    exact h
  · have hq' : U (-(liftZ q)) ≠ ⊤ := by
      change LiftedFunctionL g2 (- -(liftZ q)) ≠ ⊤; rw [neg_neg, lift_eval]; exact hq
    have h := hmaxU.2 (-(liftZ q)) hq'
    have eq1 : iv U (-(liftZ q)) = iv g2 q := by
      show iv G2 (- -(liftZ q)) = iv g2 q
      rw [neg_neg]; exact iv_congr (lift_eval g2 q)
    have eq0 : iv U (-Z2) = iv g2 p2s := by
      show iv G2 (- -Z2) = iv g2 p2s
      rw [neg_neg, hivZ2]
    have id1 : idot (-y) (-(liftZ q)) = idot (fun v => y (some v)) q := by
      rw [← idot_lift hsum_y q]; simp [idot]
    have id2 : idot (-y) (-Z2) = idot (fun v => y (some v)) p2s := by
      rw [← idot_lift hsum_y p2s]; simp [idot, Z2]
    rw [id1, id2, eq1, eq0] at h
    exact h

end LiftSubgrad

section SepDisj
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sep_disjoint {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1 : LNaturalConvex g1) (hg2 : LNaturalConvex g2)
    {p1_0 p2_0 : V → ℤ} (hp1_0 : g1 p1_0 ≠ ⊤) (hp2_0 : g2 p2_0 ≠ ⊤)
    {p0 : V → ℤ} (hdisj : ∀ p1 p2 : V → ℤ, p0 = p1 + p2 → g1 p1 = ⊤ ∨ g2 p2 = ⊤) :
    ∃ d : V → ℤ, ∀ p1 p2 : V → ℤ, g1 p1 ≠ ⊤ → g2 p2 ≠ ⊤ →
      idot d (p1 + p2) ≤ idot d p0 - 1 := by
  let G1 := LiftedFunctionL g1
  let G2 := LiftedFunctionL g2
  have hs1 : SBF G1 := hg1.1
  have hs2 : SBF G2 := hg2.1
  have hG1_tr : ∀ W, G1 (W + 1) = G1 W := lift_tr g1
  have hG2_tr : ∀ W, G2 (W + 1) = G2 W := lift_tr g2
  let P0 := liftZ p0
  let D1 : Set (Option V → ℤ) := {W | G2 (P0 - W) ≠ ⊤}
  let D2 : Set (Option V → ℤ) := {W | G1 W ≠ ⊤}
  have hD1 : DiscreteConvex.LConvexSets.LConvexSet D1 := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · have ha' : G2 (P0 - a) ≠ ⊤ := ha
      have hb' : G2 (P0 - b) ≠ ⊤ := hb
      have hs := hs2 (P0 - a) (P0 - b)
      have e_sup : (P0 - a) ⊔ (P0 - b) = P0 - (a ⊓ b) := by
        funext o; show max (P0 o - a o) (P0 o - b o) = P0 o - min (a o) (b o); omega
      have e_inf : (P0 - a) ⊓ (P0 - b) = P0 - (a ⊔ b) := by
        funext o; show min (P0 o - a o) (P0 o - b o) = P0 o - max (a o) (b o); omega
      rw [e_sup, e_inf] at hs
      have hfin := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨ha', hb'⟩) hs
      exact ⟨(WithTop.add_ne_top.1 hfin).2, (WithTop.add_ne_top.1 hfin).1⟩
    · have ha' : G2 (P0 - a) ≠ ⊤ := ha
      refine ⟨?_, ?_⟩
      · show G2 (P0 - (fun o => a o + 1)) ≠ ⊤
        have e : P0 - a = (P0 - fun o => a o + 1) + 1 := by funext o; simp; ring
        rw [e, hG2_tr] at ha'; exact ha'
      · show G2 (P0 - (fun o => a o - 1)) ≠ ⊤
        have e : P0 - (fun o => a o - 1) = (P0 - a) + 1 := by funext o; simp; ring
        rw [e, hG2_tr]; exact ha'
  have hD2 : DiscreteConvex.LConvexSets.LConvexSet D2 := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · have hs := hs1 a b
      have hfin := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨ha, hb⟩) hs
      exact WithTop.add_ne_top.1 hfin
    · have ha' : G1 a ≠ ⊤ := ha
      refine ⟨?_, ?_⟩
      · show G1 (a + 1) ≠ ⊤; rw [hG1_tr]; exact ha'
      · show G1 (fun o => a o - 1) ≠ ⊤
        have e : a = (fun o => a o - 1) + 1 := by funext o; simp
        rw [e, hG1_tr] at ha'; exact ha'
  have hDdisj : D1 ∩ D2 = ∅ := by
    ext W
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h2, h1⟩
    let p1 : V → ℤ := fun v => W (some v) - W none
    let p2 : V → ℤ := fun v => (P0 - W) (some v) - (P0 - W) none
    have hp : p0 = p1 + p2 := by
      funext v; simp [p1, p2, P0, liftZ]
    rcases hdisj p1 p2 hp with ht1 | ht2
    · exact h1 ht1
    · exact h2 ht2
  obtain ⟨Y, -, hsep⟩ :=
    DiscreteConvex.LConvexSets.discrete_separation_lconvex D1 D2 hD1 hD2 hDdisj
  have hle : ∀ W1 ∈ D2, ∀ W2 ∈ D1, idot Y W1 + 1 ≤ idot Y W2 := by
    intro W1 hW1 W2 hW2
    have h1 : (((∑ o, (Y o : ℝ) * (W1 o : ℝ) : ℝ) : EReal)) ≤
        sSup ((fun p : Option V → ℤ => ((∑ v, (Y v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D2) :=
      le_sSup ⟨W1, hW1, rfl⟩
    have h2 : sInf ((fun p : Option V → ℤ => ((∑ v, (Y v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D1) ≤
        (((∑ o, (Y o : ℝ) * (W2 o : ℝ) : ℝ) : EReal)) :=
      sInf_le ⟨W2, hW2, rfl⟩
    have h3 : (((∑ o, (Y o : ℝ) * (W1 o : ℝ) : ℝ) : EReal)) + 1 ≤
        (((∑ o, (Y o : ℝ) * (W2 o : ℝ) : ℝ) : EReal)) :=
      (add_le_add_left h1 1).trans (hsep.trans h2)
    rw [dot_eq, dot_eq] at h3
    change (((idot Y W1 : ℤ) : ℝ) : EReal) + ((1 : ℝ) : EReal) ≤
      (((idot Y W2 : ℤ) : ℝ) : EReal) at h3
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have h4 : ((idot Y W1 + 1 : ℤ) : ℝ) ≤ ((idot Y W2 : ℤ) : ℝ) := by push_cast; exact h3
    exact_mod_cast h4
  have hW1_0 : liftZ p1_0 ∈ D2 := by
    change LiftedFunctionL g1 (liftZ p1_0) ≠ ⊤; rw [lift_eval]; exact hp1_0
  have hW2_0 : P0 - liftZ p2_0 ∈ D1 := by
    change LiftedFunctionL g2 (P0 - (P0 - liftZ p2_0)) ≠ ⊤
    rw [sub_sub_cancel, lift_eval]; exact hp2_0
  have hsumY : ∑ o : Option V, Y o = 0 := by
    let C : ℤ := idot Y (P0 - liftZ p2_0) - idot Y (liftZ p1_0)
    by_contra hne
    have hshift : ∀ k : ℕ, (fun o => liftZ p1_0 o + (k : ℤ)) ∈ D2 ∧
        (fun o => liftZ p1_0 o - (k : ℤ)) ∈ D2 := by
      intro k
      induction k with
      | zero => simp [hW1_0]
      | succ k ih =>
        refine ⟨?_, ?_⟩
        · convert (hD2.2 _ ih.1).1 using 2; push_cast; ring
        · convert (hD2.2 _ ih.2).2 using 2; push_cast; ring
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · set k := C.natAbs + 1
      have hk := hle _ (hshift k).2 _ hW2_0
      have hid : idot Y (fun o => liftZ p1_0 o - (k : ℤ)) =
          idot Y (liftZ p1_0) - (k : ℤ) * ∑ o, Y o := by
        simp only [idot, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        refine congrArg (∑ x, Y x * liftZ p1_0 x - ·) (Finset.sum_congr rfl fun o _ => mul_comm _ _)
      rw [hid] at hk
      have : (k : ℤ) * (-(∑ o, Y o)) ≥ (k : ℤ) * 1 :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      have : C ≤ (C.natAbs : ℤ) := Int.le_natAbs
      dsimp [C, k] at hk this ⊢
      nlinarith
    · set k := C.natAbs + 1
      have hk := hle _ (hshift k).1 _ hW2_0
      have hid : idot Y (fun o => liftZ p1_0 o + (k : ℤ)) =
          idot Y (liftZ p1_0) + (k : ℤ) * ∑ o, Y o := by
        simp only [idot, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        refine congrArg (∑ x, Y x * liftZ p1_0 x + ·) (Finset.sum_congr rfl fun o _ => mul_comm _ _)
      rw [hid] at hk
      have : (k : ℤ) * (∑ o, Y o) ≥ (k : ℤ) * 1 :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      have : C ≤ (C.natAbs : ℤ) := Int.le_natAbs
      dsimp [C, k] at hk this ⊢
      nlinarith
  refine ⟨fun v => Y (some v), fun p1 p2 hp1 hp2 => ?_⟩
  have hm1 : liftZ p1 ∈ D2 := by
    change LiftedFunctionL g1 (liftZ p1) ≠ ⊤; rw [lift_eval]; exact hp1
  have hm2 : P0 - liftZ p2 ∈ D1 := by
    change LiftedFunctionL g2 (P0 - (P0 - liftZ p2)) ≠ ⊤
    rw [sub_sub_cancel, lift_eval]; exact hp2
  have h := hle _ hm1 _ hm2
  have e2 : idot Y (P0 - liftZ p2) = idot Y P0 - idot Y (liftZ p2) := by
    simp only [idot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [e2, idot_lift hsumY p1, idot_lift hsumY p0, idot_lift hsumY p2] at h
  rw [idot_add_right]
  omega

end SepDisj

section Main
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma infconv_ne_top_destruct {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2)
    {p : V → ℤ} (hne : InfConv g1 g2 p ≠ ⊤) :
    ∃ p1s p2s : V → ℤ, p = p1s + p2s ∧ g1 p1s ≠ ⊤ ∧ g2 p2s ≠ ⊤ ∧
      InfConv g1 g2 p = g1 p1s + g2 p2s ∧
      ∀ p1 p2 : V → ℤ, p = p1 + p2 → g1 p1 ≠ ⊤ → g2 p2 ≠ ⊤ →
        iv g1 p1s + iv g2 p2s ≤ iv g1 p1 + iv g2 p2 := by
  let S : Set (WithTop ℝ) := {L | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2}
  have hIC : InfConv g1 g2 p = sInf S := rfl
  have hcond : ¬ (S ⊆ {⊤} ∨ ¬ BddBelow S) := by
    intro h
    apply hne
    change (if S ⊆ {⊤} ∨ ¬ BddBelow S then ⊤ else _) = ⊤
    rw [if_pos h]
  push Not at hcond
  obtain ⟨hnot_top, hbdd⟩ := hcond
  obtain ⟨L0, ⟨p1_0, p2_0, hp0, rfl⟩, hL0⟩ := Set.not_subset.1 hnot_top
  rw [Set.mem_singleton_iff] at hL0
  obtain ⟨hp1_0, hp2_0⟩ := WithTop.add_ne_top.1 hL0
  obtain ⟨w, hw⟩ := hbdd
  have hw_ne : w ≠ ⊤ := ne_top_of_le_ne_top hL0 (hw ⟨p1_0, p2_0, hp0, rfl⟩)
  obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.1 hw_ne
  have hlow_int : ∀ p1 p2 : V → ℤ, p = p1 + p2 → g1 p1 ≠ ⊤ → g2 p2 ≠ ⊤ →
      ⌊b⌋ ≤ iv g1 p1 + iv g2 p2 := by
    intro p1 p2 hp hp1 hp2
    have hle := hw ⟨p1, p2, hp, rfl⟩
    rw [iv_spec hg1z hp1, iv_spec hg2z hp2, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
    exact_mod_cast (Int.floor_le b).trans hle
  have hbdZ : ∃ B : ℤ, ∀ k : ℤ,
      (∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ g1 p1 ≠ ⊤ ∧ g2 p2 ≠ ⊤ ∧ k = iv g1 p1 + iv g2 p2) →
      B ≤ k := by
    refine ⟨⌊b⌋, ?_⟩
    rintro k ⟨p1, p2, hp, hp1, hp2, rfl⟩
    exact hlow_int p1 p2 hp hp1 hp2
  obtain ⟨k0, ⟨p1s, p2s, hps, hp1s, hp2s, rfl⟩, hmin⟩ :=
    Int.exists_least_of_bdd hbdZ ⟨_, p1_0, p2_0, hp0, hp1_0, hp2_0, rfl⟩
  have hneS : S.Nonempty := ⟨g1 p + g2 0, p, 0, by simp, rfl⟩
  refine ⟨p1s, p2s, hps, hp1s, hp2s, ?_, fun p1 p2 hp hp1 hp2 => hmin _ ⟨p1, p2, hp, hp1, hp2, rfl⟩⟩
  apply le_antisymm
  · exact csInf_le ⟨b, hw⟩ ⟨p1s, p2s, hps, rfl⟩
  · apply le_csInf hneS
    rintro L ⟨q1, q2, hq, rfl⟩
    by_cases hq1 : g1 q1 = ⊤
    · rw [hq1, top_add]; exact le_top
    by_cases hq2 : g2 q2 = ⊤
    · rw [hq2, add_top]; exact le_top
    rw [iv_spec hg1z hp1s, iv_spec hg2z hp2s, iv_spec hg1z hq1, iv_spec hg2z hq2,
      ← WithTop.coe_add, ← WithTop.coe_add]
    have := hmin (iv g1 q1 + iv g2 q2) ⟨q1, q2, hq, hq1, hq2, rfl⟩
    exact_mod_cast this

lemma infconv_intval {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2) :
    IsIntegerValuedFn (InfConv g1 g2) := by
  intro p
  by_cases hp : InfConv g1 g2 p = ⊤
  · exact Or.inl hp
  · obtain ⟨p1s, p2s, _, hp1s, hp2s, heq, -⟩ := infconv_ne_top_destruct hg1z hg2z hp
    right
    refine ⟨iv g1 p1s + iv g2 p2s, ?_⟩
    rw [heq, iv_spec hg1z hp1s, iv_spec hg2z hp2s, ← WithTop.coe_add]
    push_cast; rfl

lemma ismax_infconv_of_parts {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2)
    {p0 p1s p2s x : V → ℤ} (hp0 : p0 = p1s + p2s)
    (heq0 : InfConv g1 g2 p0 = g1 p1s + g2 p2s)
    (hx1 : IsMaxZ g1 x p1s) (hx2 : IsMaxZ g2 x p2s) :
    IsMaxZ (InfConv g1 g2) x p0 := by
  have hicz := infconv_intval hg1z hg2z
  have hp0_ne : InfConv g1 g2 p0 ≠ ⊤ := by
    rw [heq0]; exact WithTop.add_ne_top.2 ⟨hx1.1, hx2.1⟩
  have hiv0 : iv (InfConv g1 g2) p0 = iv g1 p1s + iv g2 p2s := by
    have s := iv_spec hicz hp0_ne
    rw [heq0, iv_spec hg1z hx1.1, iv_spec hg2z hx2.1, ← WithTop.coe_add] at s
    exact_mod_cast WithTop.coe_injective s.symm
  refine ⟨hp0_ne, fun q hq => ?_⟩
  obtain ⟨q1, q2, hq12, hq1, hq2, heqq, -⟩ := infconv_ne_top_destruct hg1z hg2z hq
  have hivq : iv (InfConv g1 g2) q = iv g1 q1 + iv g2 q2 := by
    have s := iv_spec hicz hq
    rw [heqq, iv_spec hg1z hq1, iv_spec hg2z hq2, ← WithTop.coe_add] at s
    exact_mod_cast WithTop.coe_injective s.symm
  have i1 := hx1.2 q1 hq1
  have i2 := hx2.2 q2 hq2
  have s1 : idot x p0 = idot x p1s + idot x p2s := by rw [hp0, idot_add_right]
  have s2 : idot x q = idot x q1 + idot x q2 := by rw [hq12, idot_add_right]
  omega

end Main

end L2BicAux

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityC
open L2BicAux

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g1 g2 : (V → ℤ) → WithTop ℝ) (hg1 : LNaturalConvex g1)
    (hg2 : LNaturalConvex g2) (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2) :
    ConvexConjugate (ConvexConjugate (InfConv g1 g2)) = InfConv g1 g2 := by
  have hicz := infconv_intval hg1z hg2z
  funext p0
  by_cases hne : ∃ q, InfConv g1 g2 q ≠ ⊤
  · by_cases hp0 : InfConv g1 g2 p0 = ⊤
    · rw [hp0]
      obtain ⟨q0, hq0⟩ := hne
      obtain ⟨q1s, q2s, hq0_eq, hq1s, hq2s, heq_q0, hmin_q0⟩ :=
        infconv_ne_top_destruct hg1z hg2z hq0
      obtain ⟨x0, hx01, hx02⟩ :=
        subgrad_at_min hg1 hg2 hg1z hg2z hq0_eq hq1s hq2s hmin_q0
      have hmax_q0 := ismax_infconv_of_parts hg1z hg2z hq0_eq heq_q0 hx01 hx02
      have hdisj : ∀ p1 p2 : V → ℤ, p0 = p1 + p2 → g1 p1 = ⊤ ∨ g2 p2 = ⊤ := by
        intro p1 p2 hp
        by_contra hboth
        push Not at hboth
        obtain ⟨hp1, hp2⟩ := hboth
        let S : Set (WithTop ℝ) := {L | ∃ a b : V → ℤ, p0 = a + b ∧ L = g1 a + g2 b}
        have hbdd : BddBelow S := by
          refine ⟨((((idot x0 p0 - (idot x0 q1s - iv g1 q1s) - (idot x0 q2s - iv g2 q2s) : ℤ)) : ℝ) : WithTop ℝ), ?_⟩
          rintro L ⟨a, b, hab, rfl⟩
          by_cases ha : g1 a = ⊤
          · rw [ha, top_add]; exact le_top
          by_cases hb : g2 b = ⊤
          · rw [hb, add_top]; exact le_top
          rw [iv_spec hg1z ha, iv_spec hg2z hb, ← WithTop.coe_add, WithTop.coe_le_coe]
          have i1 := hx01.2 a ha
          have i2 := hx02.2 b hb
          have hs : idot x0 p0 = idot x0 a + idot x0 b := by rw [hab, idot_add_right]
          exact_mod_cast (by omega :
            idot x0 p0 - (idot x0 q1s - iv g1 q1s) - (idot x0 q2s - iv g2 q2s) ≤ iv g1 a + iv g2 b)
        have hle : InfConv g1 g2 p0 ≤ g1 p1 + g2 p2 := csInf_le hbdd ⟨p1, p2, hp, rfl⟩
        exact (ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hp1, hp2⟩) hle) hp0
      obtain ⟨d, hd⟩ := sep_disjoint hg1 hg2 hq1s hq2s hdisj
      have hd_ic : ∀ q : V → ℤ, InfConv g1 g2 q ≠ ⊤ → idot d q ≤ idot d p0 - 1 := by
        intro q hq
        obtain ⟨q1, q2, rfl, hq1, hq2, -⟩ := infconv_ne_top_destruct hg1z hg2z hq
        exact hd q1 q2 hq1 hq2
      apply cc_top_of_unbdd
      intro M
      let c : ℤ := idot x0 p0 - (idot x0 q0 - iv (InfConv g1 g2) q0)
      let t : ℤ := max 0 (⌈M⌉ - c)
      have ht0 : 0 ≤ t := le_max_left _ _
      let X : V → ℤ := x0 + t • d
      have hX : ∀ p, idot X p = idot x0 p + t * idot d p := by
        intro p
        simp only [X, idot_add_left, idot_smul_left]
      let B : ℤ := (idot x0 q0 - iv (InfConv g1 g2) q0) + t * (idot d p0 - 1)
      have hbd : ∀ q, InfConv g1 g2 q ≠ ⊤ → idot X q - iv (InfConv g1 g2) q ≤ B := by
        intro q hq
        rw [hX]
        have h1 := hmax_q0.2 q hq
        have h2 := hd_ic q hq
        have h3 : t * idot d q ≤ t * (idot d p0 - 1) := mul_le_mul_of_nonneg_left h2 ht0
        dsimp [B]; omega
      have hfin : ConvexConjugate (InfConv g1 g2) X ≠ ⊤ :=
        cc_ne_top_of_bdd hicz ⟨q0, hq0⟩ B hbd
      obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.1 hfin
      refine ⟨X, A, hA.symm, ?_⟩
      have hAB : A ≤ ((B : ℤ) : ℝ) := by
        have := cc_le (f := InfConv g1 g2) (p := X) (C := ((B : ℤ) : ℝ)) ⟨q0, hq0⟩ (by
          intro q a ha
          rw [iv_of_eq hicz ha, dot_eq]
          exact_mod_cast hbd q (by rw [ha]; exact WithTop.coe_ne_top))
        rw [← hA, WithTop.coe_le_coe] at this
        exact this
      have e : (∑ i, (p0 i : ℝ) * (X i : ℝ)) = ((idot X p0 : ℤ) : ℝ) := by
        rw [dot_eq, idot_comm]
      rw [e, hX]
      have hge : c + t ≤ idot x0 p0 + t * idot d p0 - B := by
        dsimp [B, c]; ring_nf; omega
      have hM : M ≤ ((c + t : ℤ) : ℝ) := by
        have h1 : (⌈M⌉ : ℤ) ≤ c + t := by have := le_max_right 0 (⌈M⌉ - c); omega
        calc M ≤ (⌈M⌉ : ℝ) := Int.le_ceil M
          _ ≤ ((c + t : ℤ) : ℝ) := by exact_mod_cast h1
      have hge' : ((c + t : ℤ) : ℝ) ≤ ((idot x0 p0 + t * idot d p0 - B : ℤ) : ℝ) := by
        exact_mod_cast hge
      push_cast at hge' hM hAB ⊢
      linarith
    · obtain ⟨p1s, p2s, hp0_eq, hp1s, hp2s, heq_p0, hmin_p0⟩ :=
        infconv_ne_top_destruct hg1z hg2z hp0
      obtain ⟨x, hx1, hx2⟩ :=
        subgrad_at_min hg1 hg2 hg1z hg2z hp0_eq hp1s hp2s hmin_p0
      exact biconj_of_max hicz (ismax_infconv_of_parts hg1z hg2z hp0_eq heq_p0 hx1 hx2)
  · push Not at hne
    rw [cc_empty (cc_empty hne) p0, hne p0]
