-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDuality.discrete_conjugacy_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T18:57:32.918403+00:00
-- url     : https://prove2.me/submissions/10f1a9d2-bfdb-42cb-9f39-2631b3fb17c0

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctions_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctions_LNaturalConvex

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Pd94

open DiscreteConvex.ConjugacyDuality DiscreteConvex.MConvexFunctions DiscreteConvex.LConvexFunctions

/-! ## A. Foundation: integer pairing, integer values, conjugate bookkeeping -/

section A
variable {V : Type*} [Fintype V]

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

lemma idot_one_left (x : V → ℤ) : idot (1 : V → ℤ) x = ∑ i, x i := by
  simp [idot]

open Classical in
noncomputable def iv (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : ℤ :=
  if h : ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ) then h.choose else 0

lemma iv_spec {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {x : V → ℤ} (hx : f x ≠ ⊤) :
    f x = (((iv f x : ℤ) : ℝ) : WithTop ℝ) := by
  have h : ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ) := (hZ x).resolve_left hx
  unfold iv
  rw [dif_pos h]
  exact h.choose_spec

lemma iv_of_eq {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {x : V → ℤ} {a : ℝ}
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

/-- every term is below the conjugate -/
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

/-- `x` maximizes `⟨p, ·⟩ - f` over `dom f` (integer form). -/
def IsMaxZ (f : (V → ℤ) → WithTop ℝ) (p x : V → ℤ) : Prop :=
  f x ≠ ⊤ ∧ ∀ y, f y ≠ ⊤ → idot p y - iv f y ≤ idot p x - iv f x

lemma cc_of_max {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {p x : V → ℤ}
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

lemma cc_ge_Z {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {x : V → ℤ} (hx : f x ≠ ⊤)
    (p : V → ℤ) : ((((idot p x - iv f x : ℤ)) : ℝ) : WithTop ℝ) ≤ ConvexConjugate f p := by
  have := cc_ge (iv_spec hZ hx) p
  rw [dot_eq] at this
  exact_mod_cast this

lemma cc_attain {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {p : V → ℤ}
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

lemma cc_ne_top_of_bdd {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {p : V → ℤ}
    (hne : ∃ x, f x ≠ ⊤) (B : ℤ) (hB : ∀ y, f y ≠ ⊤ → idot p y - iv f y ≤ B) :
    ConvexConjugate f p ≠ ⊤ := by
  have : ConvexConjugate f p ≤ (((B : ℤ) : ℝ) : WithTop ℝ) := by
    apply cc_le hne
    intro y a ha
    rw [iv_of_eq hZ ha, dot_eq]
    exact_mod_cast hB y (by rw [ha]; exact WithTop.coe_ne_top)
  exact ne_top_of_le_ne_top WithTop.coe_ne_top this

/-- DC-5: the conjugate of an integer-valued function is integer valued. -/
theorem conj_intval {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) :
    IsIntegerValued (ConvexConjugate f) := by
  intro p
  by_cases hne : ∃ x, f x ≠ ⊤
  · by_cases hfin : ConvexConjugate f p = ⊤
    · exact Or.inl hfin
    · obtain ⟨x, hx⟩ := cc_attain hZ hne hfin
      exact Or.inr ⟨_, cc_of_max hZ hx⟩
  · push Not at hne
    exact Or.inl (cc_empty hne p)

end A

/-! ## B. Exchange machinery for M-convex functions (integer form) -/

section B
variable {V : Type*} [Fintype V] [DecidableEq V]

def ex (x : V → ℤ) (a b : V) : V → ℤ := fun w => x w - CharVec a w + CharVec b w

def dist1 (x y : V → ℤ) : ℕ := ∑ i, (x i - y i).natAbs

lemma dist1_comm (x y : V → ℤ) : dist1 x y = dist1 y x := by
  unfold dist1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.natAbs_neg]; congr 1; ring

lemma charvec_self (a : V) : CharVec a a = 1 := by simp [CharVec]

lemma charvec_ne {a w : V} (h : w ≠ a) : CharVec a w = 0 := by simp [CharVec, h]

lemma ex_self (x : V → ℤ) (a : V) : ex x a a = x := by
  funext w; simp only [ex]; ring

lemma ex_ex_cancel (x : V → ℤ) (a b c : V) : ex (ex x a b) b c = ex x a c := by
  funext w; simp only [ex]; ring

lemma ex_ex_swap (x : V → ℤ) (a b c : V) : ex (ex x a b) c a = ex x c b := by
  funext w; simp only [ex]; ring

lemma idot_charvec (p : V → ℤ) (a : V) : idot p (CharVec a) = p a := by
  simp [idot, CharVec]

lemma idot_charvec_left (x : V → ℤ) (a : V) : idot (CharVec a) x = x a := by
  simp [idot, CharVec]

lemma idot_ex (p x : V → ℤ) (a b : V) : idot p (ex x a b) = idot p x - p a + p b := by
  have h : ex x a b = x - CharVec a + CharVec b := by funext w; simp [ex]
  rw [h, idot_add_right, sub_eq_add_neg, idot_add_right]
  have : idot p (-CharVec a) = - p a := by
    simp only [idot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [show (∑ i, p i * CharVec a i) = idot p (CharVec a) from rfl, idot_charvec]
  rw [this, idot_charvec]; ring

lemma ex_apply (x : V → ℤ) (a b w : V) :
    ex x a b w = x w - (if w = a then 1 else 0) + (if w = b then 1 else 0) := rfl

lemma wt_sum_ne_top {A B : WithTop ℝ} {r : ℝ} (h : A + B ≤ (r : WithTop ℝ)) : A ≠ ⊤ ∧ B ≠ ⊤ := by
  constructor
  · rintro rfl; rw [top_add] at h; exact WithTop.coe_ne_top (top_le_iff.mp h)
  · rintro rfl; rw [add_top] at h; exact WithTop.coe_ne_top (top_le_iff.mp h)

/-- M-EXC in integer form. -/
lemma mexcZ {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {x y : V → ℤ} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) {u : V} (hu : y u < x u) :
    ∃ v, x v < y v ∧ f (ex x u v) ≠ ⊤ ∧ f (ex y v u) ≠ ⊤ ∧
      iv f (ex x u v) + iv f (ex y v u) ≤ iv f x + iv f y := by
  obtain ⟨v, hv, h⟩ := hf x hx y hy u (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩)
  have hv' : x v < y v := (Finset.mem_filter.1 hv).2
  have e : (fun w => y w + CharVec u w - CharVec v w) = ex y v u := by
    funext w; simp only [ex]; ring
  have e2 : (fun w => x w - CharVec u w + CharVec v w) = ex x u v := rfl
  rw [e, e2] at h
  rw [iv_spec hZ hx, iv_spec hZ hy, ← WithTop.coe_add] at h
  obtain ⟨h1, h2⟩ := wt_sum_ne_top h
  refine ⟨v, hv', h1, h2, ?_⟩
  rw [iv_spec hZ h1, iv_spec hZ h2, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at h
  exact_mod_cast h

lemma exists_pos_of_ne {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {x y : V → ℤ} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) (hne : y ≠ x) : ∃ u, x u < y u := by
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hi' : y i < x i := lt_of_le_of_ne (h i) hi
  obtain ⟨v, hv, -⟩ := mexcZ hf hZ hx hy hi'
  have := h v
  omega

lemma dist_ex_lt {y x0 : V → ℤ} {u v : V} (hu : x0 u < y u) (hv : y v < x0 v) :
    dist1 (ex y u v) x0 < dist1 y x0 := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    rw [ex_apply]
    split_ifs with h1 h2 h2 <;> subst_vars <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    rw [ex_apply, if_pos rfl, if_neg huv]
    omega

/-- Local optimality ⇒ global optimality (Murota Thm 6.26), integer form. -/
theorem local_optZ {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {x0 : V → ℤ} (hx0 : f x0 ≠ ⊤) (p : V → ℤ)
    (hloc : ∀ a b, f (ex x0 a b) ≠ ⊤ →
      idot p (ex x0 a b) - iv f (ex x0 a b) ≤ idot p x0 - iv f x0) : IsMaxZ f p x0 := by
  refine ⟨hx0, ?_⟩
  suffices H : ∀ n : ℕ, ∀ y, dist1 y x0 < n → f y ≠ ⊤ →
      idot p y - iv f y ≤ idot p x0 - iv f x0 from
    fun y hy => H _ y (Nat.lt_succ_self _) hy
  intro n
  induction n with
  | zero => intro y h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro y hn hy
    by_cases hyx : y = x0
    · rw [hyx]
    obtain ⟨u, hu⟩ := exists_pos_of_ne hf hZ hx0 hy hyx
    obtain ⟨v, hv, h1, h2, h⟩ := mexcZ hf hZ hy hx0 hu
    have hd := dist_ex_lt hu hv
    have h3 := ih (ex y u v) (by omega) h1
    have h4 := hloc v u h2
    rw [idot_ex] at h3 h4
    linarith

/-- Triangle inequality of exchange weights. -/
theorem triangleZ {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    (x : V → ℤ) {a b d : V} (hab : a ≠ b) (hbd : b ≠ d)
    (h1 : f (ex x a b) ≠ ⊤) (h2 : f (ex x b d) ≠ ⊤) :
    f x ≠ ⊤ ∧ f (ex x a d) ≠ ⊤ ∧
      iv f x + iv f (ex x a d) ≤ iv f (ex x a b) + iv f (ex x b d) := by
  have hu : (ex x b d) b < (ex x a b) b := by
    simp only [ex_apply]
    split_ifs <;> simp_all
  obtain ⟨v, hv, h3, h4, h⟩ := mexcZ hf hZ h1 h2 hu
  have hv' : v = a ∨ v = d := by
    by_contra hc
    push Not at hc
    rw [ex_apply, ex_apply, if_neg hc.1, if_neg hc.2] at hv
    split_ifs at hv <;> omega
  rcases hv' with rfl | rfl
  · simp only [ex_ex_cancel, ex_self, ex_ex_swap] at h h3 h4
    exact ⟨h3, h4, h⟩
  · simp only [ex_ex_cancel, ex_self] at h h3 h4
    exact ⟨h4, h3, by linarith⟩

/-- Integer subgradient of an integer M-convex function (Murota Thm 6.61, via potentials). -/
theorem subgrad_M {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {x : V → ℤ} (hx : f x ≠ ⊤) : ∃ p : V → ℤ, IsMaxZ f p x := by
  classical
  let ℓ : V → V → ℤ := fun a b => iv f (ex x a b) - iv f x
  let A : V → Finset V := fun b => Finset.univ.filter (fun a => f (ex x a b) ≠ ⊤)
  have hA : ∀ b, (A b).Nonempty := fun b =>
    ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [ex_self]; exact hx⟩⟩
  have hAi : ∀ b, ((A b).image (fun a => ℓ a b)).Nonempty := fun b => (hA b).image _
  let d : V → ℤ := fun b => ((A b).image (fun a => ℓ a b)).min' (hAi b)
  have hd1 : ∀ a b, f (ex x a b) ≠ ⊤ → d b ≤ ℓ a b := fun a b h =>
    Finset.min'_le _ _ (Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩)
  have hd2 : ∀ b, ∃ a, f (ex x a b) ≠ ⊤ ∧ d b = ℓ a b := by
    intro b
    obtain ⟨a, ha, he⟩ := Finset.mem_image.1 (Finset.min'_mem _ (hAi b))
    exact ⟨a, (Finset.mem_filter.1 ha).2, he.symm⟩
  refine ⟨d, local_optZ hf hZ hx d ?_⟩
  intro a b hab
  rw [idot_ex]
  suffices d b ≤ d a + ℓ a b by simp only [ℓ] at this; linarith
  obtain ⟨a0, h0, e0⟩ := hd2 a
  by_cases hab' : a = b
  · subst hab'; simp only [ℓ, ex_self]; omega
  by_cases ha0 : a0 = a
  · subst ha0
    have : ℓ a0 a0 = 0 := by simp only [ℓ, ex_self]; ring
    rw [e0, this]; simpa using hd1 a0 b hab
  obtain ⟨-, h5, h6⟩ := triangleZ hf hZ x ha0 hab' h0 hab
  have := hd1 a0 b h5
  simp only [ℓ] at this e0 ⊢
  linarith

end B

/-! ## C. Domain indicator, hyperplane, nearest point, separation; DC-2 (M biconjugacy) -/

section C
variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
noncomputable def ind (f : (V → ℤ) → WithTop ℝ) : (V → ℤ) → WithTop ℝ :=
  fun z => if f z = ⊤ then ⊤ else 0

lemma ind_ne_top {f : (V → ℤ) → WithTop ℝ} {z : V → ℤ} : ind f z ≠ ⊤ ↔ f z ≠ ⊤ := by
  unfold ind
  split_ifs with h
  · simp [h]
  · simp [h]

lemma ind_intval (f : (V → ℤ) → WithTop ℝ) : IsIntegerValued (ind f) := by
  intro z
  unfold ind
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr ⟨0, by simp⟩

lemma iv_ind {f : (V → ℤ) → WithTop ℝ} {z : V → ℤ} (hz : f z ≠ ⊤) : iv (ind f) z = 0 := by
  have h : ind f z = ((0 : ℝ) : WithTop ℝ) := by simp [ind, hz]
  have := iv_of_eq (ind_intval f) h
  exact_mod_cast this.symm

lemma ind_mexc {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f) :
    MExchangeAxiom (ind f) := by
  intro x hx y hy u hu
  have hx' : f x ≠ ⊤ := ind_ne_top.1 hx
  have hy' : f y ≠ ⊤ := ind_ne_top.1 hy
  obtain ⟨v, hv, h⟩ := hf x hx' y hy' u hu
  rw [iv_spec hZ hx', iv_spec hZ hy', ← WithTop.coe_add] at h
  obtain ⟨h1, h2⟩ := wt_sum_ne_top h
  refine ⟨v, hv, ?_⟩
  simp [ind, hx', hy', h1, h2]

/-- `x0 ∈ dom f` maximizes `⟨q, ·⟩` over `dom f` given the local condition. -/
lemma lin_max {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {x0 : V → ℤ} (hx0 : f x0 ≠ ⊤) (q : V → ℤ)
    (hloc : ∀ a b, f (ex x0 a b) ≠ ⊤ → q b ≤ q a) : ∀ z, f z ≠ ⊤ → idot q z ≤ idot q x0 := by
  have H := local_optZ (ind_mexc hf hZ) (ind_intval f) (ind_ne_top.2 hx0) q (by
    intro a b hab
    have hab' := ind_ne_top.1 hab
    rw [iv_ind hab', iv_ind hx0, idot_ex]
    have := hloc a b hab'
    omega)
  intro z hz
  have := H.2 z (ind_ne_top.2 hz)
  rw [iv_ind hz, iv_ind hx0] at this
  omega

lemma sum_const {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {y z : V → ℤ} (hy : f y ≠ ⊤) (hz : f z ≠ ⊤) : ∑ i, z i = ∑ i, y i := by
  have h1 := lin_max hf hZ hy 1 (fun a b _ => le_rfl) z hz
  have h2 := lin_max hf hZ hz 1 (fun a b _ => le_rfl) y hy
  rw [idot_one_left, idot_one_left] at h1 h2
  omega

lemma nearest {f : (V → ℤ) → WithTop ℝ} (hne : ∃ y, f y ≠ ⊤) (x : V → ℤ) :
    ∃ y, f y ≠ ⊤ ∧ ∀ z, f z ≠ ⊤ → dist1 y x ≤ dist1 z x := by
  classical
  have h : ∃ n, ∃ y, f y ≠ ⊤ ∧ dist1 y x = n := by
    obtain ⟨y, hy⟩ := hne; exact ⟨_, y, hy, rfl⟩
  obtain ⟨y, hy, hn⟩ := Nat.find_spec h
  exact ⟨y, hy, fun z hz => hn ▸ Nat.find_min' h ⟨z, hz, rfl⟩⟩

/-- Separation of a point outside `dom f` (nearest-point argument). -/
theorem sep_M {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {x y : V → ℤ} (hy : f y ≠ ⊤) (hx : f x = ⊤)
    (hnear : ∀ z, f z ≠ ⊤ → dist1 y x ≤ dist1 z x) :
    ∃ q : V → ℤ, (∀ z, f z ≠ ⊤ → idot q z ≤ idot q y) ∧ idot q y < idot q x := by
  classical
  have hdom : ∀ z, f z ≠ ⊤ → ∑ i, z i = ∑ i, y i := fun z hz => sum_const hf hZ hy hz
  by_cases hs : ∑ i, x i = ∑ i, y i
  · -- the exchange-graph construction
    let T : Finset V := Finset.univ.filter (fun b => ∃ a, x a < y a ∧ f (ex y a b) ≠ ⊤)
    have hT : ∀ b, b ∈ T ↔ ∃ a, x a < y a ∧ f (ex y a b) ≠ ⊤ := fun b => by simp [T]
    let q : V → ℤ := fun w => if w ∈ T then 0 else 1
    have hfwd : ∀ a b, a ∈ T → f (ex y a b) ≠ ⊤ → b ∈ T := by
      intro a b ha hab
      obtain ⟨a0, h0, h0'⟩ := (hT a).1 ha
      by_cases hab' : a = b
      · rw [← hab']; exact ha
      by_cases ha0 : a0 = a
      · subst ha0; exact (hT b).2 ⟨a0, h0, hab⟩
      obtain ⟨-, h5, -⟩ := triangleZ hf hZ y ha0 hab' h0' hab
      exact (hT b).2 ⟨a0, h0, h5⟩
    have hdisj : ∀ b, b ∈ T → x b ≤ y b := by
      intro b hb
      obtain ⟨a, ha, hab⟩ := (hT b).1 hb
      by_contra hc
      push Not at hc
      have := dist_ex_lt (x0 := x) ha hc
      have := hnear _ hab
      omega
    refine ⟨q, ?_, ?_⟩
    · apply lin_max hf hZ hy q
      intro a b hab
      by_cases ha : a ∈ T
      · have hb := hfwd a b ha hab
        simp [q, ha, hb]
      · simp only [q, if_neg ha]
        split_ifs <;> omega
    · -- strictness
      have hxy : x ≠ y := by rintro rfl; exact hy hx
      obtain ⟨w0, hw0⟩ : ∃ w, x w < y w := by
        by_contra hc
        push Not at hc
        have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hc i)).1 hs.symm
        exact hxy (funext fun i => (this i (Finset.mem_univ _)).symm)
      have hw0T : w0 ∈ T := (hT w0).2 ⟨w0, hw0, by rw [ex_self]; exact hy⟩
      have key : ∑ w, (1 - q w) * (x w - y w) < ∑ _w : V, (0 : ℤ) := by
        apply Finset.sum_lt_sum
        · intro w _
          by_cases hw : w ∈ T
          · have := hdisj w hw
            simp only [q, if_pos hw]; nlinarith
          · simp [q, hw]
        · exact ⟨w0, Finset.mem_univ _, by simp only [q, if_pos hw0T]; nlinarith⟩
      have e1 : idot q x - idot q y = ∑ w, (x w - y w) - ∑ w, (1 - q w) * (x w - y w) := by
        simp only [idot, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w _ => by ring
      have e2 : ∑ w, (x w - y w) = 0 := by rw [Finset.sum_sub_distrib, hs]; ring
      simp only [Finset.sum_const_zero] at key
      omega
  · rcases lt_or_gt_of_ne hs with hlt | hgt
    · refine ⟨-1, ?_, ?_⟩
      · intro z hz
        have := hdom z hz
        simp only [idot, Pi.neg_apply, Pi.one_apply, neg_mul, one_mul, Finset.sum_neg_distrib]
        omega
      · simp only [idot, Pi.neg_apply, Pi.one_apply, neg_mul, one_mul, Finset.sum_neg_distrib]
        omega
    · refine ⟨1, ?_, ?_⟩
      · intro z hz
        rw [idot_one_left, idot_one_left, hdom z hz]
      · rw [idot_one_left, idot_one_left]; exact hgt

lemma biconj_of_max {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {x p : V → ℤ}
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

/-- DC-2: biconjugacy for integer-valued M-convex functions. -/
theorem mconv_biconj {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f) :
    ConvexConjugate (ConvexConjugate f) = f := by
  funext x
  by_cases hne : ∃ y, f y ≠ ⊤
  · by_cases hx : f x = ⊤
    · rw [hx]
      obtain ⟨y, hy, hnear⟩ := nearest hne x
      obtain ⟨q, hq1, hq2⟩ := sep_M hf hZ hy hx hnear
      obtain ⟨p0, hp0⟩ := subgrad_M hf hZ hy
      apply cc_top_of_unbdd
      intro M
      let c : ℤ := idot p0 x - idot p0 y + iv f y
      let t : ℤ := max 0 (⌈M⌉ - c)
      have ht0 : 0 ≤ t := le_max_left _ _
      have hmax : IsMaxZ f (p0 + t • q) y := by
        refine ⟨hy, fun z hz => ?_⟩
        rw [idot_add_left, idot_add_left, idot_smul_left, idot_smul_left]
        have h1 := hp0.2 z hz
        have h2 := mul_le_mul_of_nonneg_left (hq1 z hz) ht0
        linarith
      refine ⟨p0 + t • q, _, cc_of_max hZ hmax, ?_⟩
      have e : (∑ i, (x i : ℝ) * ((p0 + t • q) i : ℝ)) = ((idot (p0 + t • q) x : ℤ) : ℝ) := by
        rw [dot_eq, idot_comm]
      rw [e]
      have hge : c + t ≤ idot (p0 + t • q) x - (idot (p0 + t • q) y - iv f y) := by
        rw [idot_add_left, idot_add_left, idot_smul_left, idot_smul_left]
        have : t * idot q y + t ≤ t * idot q x := by nlinarith
        simp only [c]; linarith
      have hM : M ≤ ((c + t : ℤ) : ℝ) := by
        have h1 : (⌈M⌉ : ℤ) ≤ c + t := by have := le_max_right 0 (⌈M⌉ - c); omega
        calc M ≤ (⌈M⌉ : ℝ) := Int.le_ceil M
          _ ≤ ((c + t : ℤ) : ℝ) := by exact_mod_cast h1
      have : ((c + t : ℤ) : ℝ) ≤ ((idot (p0 + t • q) x - (idot (p0 + t • q) y - iv f y) : ℤ) : ℝ) := by
        exact_mod_cast hge
      push_cast at this hM ⊢
      linarith
    · obtain ⟨p, hp⟩ := subgrad_M hf hZ hx
      exact biconj_of_max hZ hp
  · push Not at hne
    rw [cc_empty (cc_empty hne) x, hne x]

end C

/-! ## D. DC-1: the conjugate of an integer M-convex function is L-convex -/

section D
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mconv_trf {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f) :
    TRF (ConvexConjugate f) := by
  by_cases hne : ∃ y, f y ≠ ⊤
  · obtain ⟨y0, hy0⟩ := hne
    refine ⟨((∑ i, y0 i : ℤ) : ℝ), fun p => ?_⟩
    have hshift : ∀ z, f z ≠ ⊤ → idot (p + 1) z = idot p z + ∑ i, y0 i := fun z hz => by
      rw [idot_add_left, idot_one_left, sum_const hf hZ hy0 hz]
    by_cases hp : ConvexConjugate f p = ⊤
    · rw [hp, top_add]
      by_contra hc
      obtain ⟨x, hx⟩ := cc_attain hZ ⟨y0, hy0⟩ hc
      refine absurd hp (cc_ne_top_of_bdd hZ ⟨y0, hy0⟩ (idot (p + 1) x - iv f x - ∑ i, y0 i) ?_)
      intro z hz
      have := hx.2 z hz
      rw [hshift z hz] at this
      linarith
    · obtain ⟨x, hx⟩ := cc_attain hZ ⟨y0, hy0⟩ hp
      have hx' : IsMaxZ f (p + 1) x := ⟨hx.1, fun z hz => by
        rw [hshift z hz, hshift x hx.1]; linarith [hx.2 z hz]⟩
      rw [cc_of_max hZ hx', cc_of_max hZ hx, ← WithTop.coe_add, hshift x hx.1]
      congr 1; push_cast; ring
  · push Not at hne
    exact ⟨0, fun p => by rw [cc_empty hne, cc_empty hne, top_add]⟩

lemma idot_P (p x : V → ℤ) (u v : V) :
    idot (p + CharVec u + CharVec v) x = idot p x + x u + x v := by
  rw [idot_add_left, idot_add_left, idot_charvec_left, idot_charvec_left]

lemma idot_P1 (p x : V → ℤ) (u : V) : idot (p + CharVec u) x = idot p x + x u := by
  rw [idot_add_left, idot_charvec_left]

/-- closest pair of maximizers -/
lemma local_pair {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {p : V → ℤ} {u v : V} (huv : u ≠ v) :
    ∀ n : ℕ, ∀ x y, dist1 x y < n → IsMaxZ f (p + CharVec u + CharVec v) x → IsMaxZ f p y →
      ∃ x' y', IsMaxZ f (p + CharVec u + CharVec v) x' ∧ IsMaxZ f p y' ∧
        (x' v ≤ y' v ∨ x' u ≤ y' u) := by
  intro n
  induction n with
  | zero => intro x y h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x y hd hx hy
    by_cases hc : x v ≤ y v ∨ x u ≤ y u
    · exact ⟨x, y, hx, hy, hc⟩
    push Not at hc
    obtain ⟨hcv, hcu⟩ := hc
    obtain ⟨w, hw, h1, h2, h⟩ := mexcZ hf hZ hx.1 hy.1 hcu
    have hwu : w ≠ u := by rintro rfl; omega
    have hwv : w ≠ v := by rintro rfl; omega
    have hy1 := hy.2 _ h2
    have hx1 := hx.2 _ h1
    rw [idot_ex] at hy1 hx1
    have hPu : (p + CharVec u + CharVec v) u = p u + 1 := by
      simp [CharVec, huv]
    have hPw : (p + CharVec u + CharVec v) w = p w := by
      simp [CharVec, hwu, hwv]
    rw [hPu, hPw] at hx1
    by_cases hA : iv f (ex y w u) - iv f y = p u - p w
    · have hy' : IsMaxZ f p (ex y w u) := ⟨h2, fun z hz => by
        rw [idot_ex]; linarith [hy.2 z hz]⟩
      have hd' : dist1 x (ex y w u) < dist1 x y := by
        rw [dist1_comm x, dist1_comm x]; exact dist_ex_lt hw hcu
      exact ih x (ex y w u) (by omega) hx hy'
    · have hx' : IsMaxZ f (p + CharVec u + CharVec v) (ex x u w) := ⟨h1, fun z hz => by
        rw [idot_ex, hPu, hPw]; have := hx.2 z hz; omega⟩
      have hd' : dist1 (ex x u w) y < dist1 x y := dist_ex_lt hcu hw
      exact ih _ y (by omega) hx' hy

lemma local_sbf {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f)
    {p : V → ℤ} {u v : V} (huv : u ≠ v) {x y : V → ℤ}
    (hx : IsMaxZ f (p + CharVec u + CharVec v) x) (hy : IsMaxZ f p y) :
    ConvexConjugate f p + ConvexConjugate f (p + CharVec u + CharVec v) ≤
      ConvexConjugate f (p + CharVec u) + ConvexConjugate f (p + CharVec v) := by
  obtain ⟨x', y', hx', hy', hc⟩ := local_pair hf hZ huv _ x y (Nat.lt_succ_self _) hx hy
  rw [cc_of_max hZ hx', cc_of_max hZ hy', idot_P]
  rcases hc with hc | hc
  · calc _ ≤ ((((idot (p + CharVec u) x' - iv f x' : ℤ)) : ℝ) : WithTop ℝ) +
            ((((idot (p + CharVec v) y' - iv f y' : ℤ)) : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, idot_P1, idot_P1]
          have : ((x' v : ℤ) : ℝ) ≤ ((y' v : ℤ) : ℝ) := by exact_mod_cast hc
          push_cast; linarith
      _ ≤ _ := add_le_add (cc_ge_Z hZ hx'.1 _) (cc_ge_Z hZ hy'.1 _)
  · calc _ ≤ ((((idot (p + CharVec u) y' - iv f y' : ℤ)) : ℝ) : WithTop ℝ) +
            ((((idot (p + CharVec v) x' - iv f x' : ℤ)) : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, idot_P1, idot_P1]
          have : ((x' u : ℤ) : ℝ) ≤ ((y' u : ℤ) : ℝ) := by exact_mod_cast hc
          push_cast; linarith
      _ ≤ _ := add_le_add (cc_ge_Z hZ hy'.1 _) (cc_ge_Z hZ hx'.1 _)

lemma sum_charvec (v : V) : ∑ i, CharVec v i = 1 := by simp [CharVec]

/-- Local submodularity implies submodularity for a finite-valued function on `ℤ^V`. -/
theorem lattice_sbf (G : (V → ℤ) → ℤ)
    (hloc : ∀ p u v, u ≠ v →
      G p + G (p + CharVec u + CharVec v) ≤ G (p + CharVec u) + G (p + CharVec v)) :
    ∀ p q, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q := by
  have step1 : ∀ n : ℕ, ∀ (a β : V → ℤ) (u : V), (∀ i, 0 ≤ β i) → β u = 0 →
      ∑ i, β i = n → G (a + CharVec u + β) + G a ≤ G (a + CharVec u) + G (a + β) := by
    intro n
    induction n with
    | zero =>
      intro a β u hβ _ hs
      have h0 : β = 0 := funext fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hβ i)).1 (by exact_mod_cast hs) i
          (Finset.mem_univ _)
      subst h0; simp only [add_zero]; linarith
    | succ n ih =>
      intro a β u hβ hu hs
      obtain ⟨v, hv⟩ : ∃ v, 0 < β v := by
        by_contra hc
        push Not at hc
        have : ∑ i, β i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
        omega
      have huv : u ≠ v := by rintro rfl; omega
      have h1 := ih a (β - CharVec v) u (fun i => by
          simp only [Pi.sub_apply, CharVec]; split_ifs with h
          · subst h; omega
          · have := hβ i; omega)
        (by simp [CharVec, huv, hu])
        (by simp only [Pi.sub_apply]; rw [Finset.sum_sub_distrib, sum_charvec, hs]; push_cast; ring)
      have h2 := hloc (a + (β - CharVec v)) u v huv
      have e1 : a + (β - CharVec v) + CharVec u + CharVec v = a + CharVec u + β := by
        funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
      have e2 : a + (β - CharVec v) + CharVec u = a + CharVec u + (β - CharVec v) := by
        funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
      have e3 : a + (β - CharVec v) + CharVec v = a + β := by
        funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [e1, e2, e3] at h2
      linarith
  have step2 : ∀ n : ℕ, ∀ (a α β : V → ℤ), (∀ i, 0 ≤ α i) → (∀ i, 0 ≤ β i) →
      (∀ i, α i = 0 ∨ β i = 0) → ∑ i, α i = n →
      G (a + α + β) + G a ≤ G (a + α) + G (a + β) := by
    intro n
    induction n with
    | zero =>
      intro a α β hα _ _ hs
      have h0 : α = 0 := funext fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hα i)).1 (by exact_mod_cast hs) i
          (Finset.mem_univ _)
      subst h0; simp only [add_zero]; linarith
    | succ n ih =>
      intro a α β hα hβ hd hs
      obtain ⟨u, hu⟩ : ∃ u, 0 < α u := by
        by_contra hc
        push Not at hc
        have : ∑ i, α i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
        omega
      have hβu : β u = 0 := (hd u).resolve_left (by omega)
      have h1 := ih a (α - CharVec u) β (fun i => by
          simp only [Pi.sub_apply, CharVec]; split_ifs with h
          · subst h; omega
          · have := hα i; omega) hβ
        (fun i => by
          simp only [Pi.sub_apply, CharVec]; split_ifs with h
          · subst h; right; exact hβu
          · rcases hd i with h' | h'
            · left; omega
            · right; exact h')
        (by simp only [Pi.sub_apply]; rw [Finset.sum_sub_distrib, sum_charvec, hs]; push_cast; ring)
      have h2 := step1 (∑ i, β i).toNat (a + (α - CharVec u)) β u hβ hβu
        (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hβ i)).symm
      have e1 : a + (α - CharVec u) + CharVec u + β = a + α + β := by
        funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
      have e2 : a + (α - CharVec u) + CharVec u = a + α := by
        funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [e1, e2] at h2
      linarith
  intro p q
  have hsum : 0 ≤ ∑ i, (p - p ⊓ q) i := Finset.sum_nonneg fun i _ => by
    simp only [Pi.sub_apply, Pi.inf_apply]; have := inf_le_left (a := p i) (b := q i); omega
  have h := step2 (∑ i, (p - p ⊓ q) i).toNat (p ⊓ q) (p - p ⊓ q) (q - p ⊓ q)
    (fun i => by simp only [Pi.sub_apply, Pi.inf_apply]; have := inf_le_left (a := p i) (b := q i); omega)
    (fun i => by simp only [Pi.sub_apply, Pi.inf_apply]; have := inf_le_right (a := p i) (b := q i); omega)
    (fun i => by
      simp only [Pi.sub_apply, Pi.inf_apply]
      rcases le_total (p i) (q i) with h | h
      · left; rw [inf_eq_left.2 h]; ring
      · right; rw [inf_eq_right.2 h]; ring)
    (Int.toNat_of_nonneg hsum).symm
  have e1 : p ⊓ q + (p - p ⊓ q) + (q - p ⊓ q) = p ⊔ q := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.inf_apply, Pi.sup_apply]
    rcases le_total (p i) (q i) with h | h
    · rw [inf_eq_left.2 h, sup_eq_right.2 h]; ring
    · rw [inf_eq_right.2 h, sup_eq_left.2 h]; ring
  have e2 : p ⊓ q + (p - p ⊓ q) = p := by funext i; simp
  have e3 : p ⊓ q + (q - p ⊓ q) = q := by funext i; simp
  rw [e1, e2, e3] at h
  linarith

open Classical in
noncomputable def trunc (N : ℤ) (f : (V → ℤ) → WithTop ℝ) : (V → ℤ) → WithTop ℝ :=
  fun z => if ∀ i, |z i| ≤ N then f z else ⊤

lemma trunc_ne_top {N : ℤ} {f : (V → ℤ) → WithTop ℝ} {z : V → ℤ} :
    trunc N f z ≠ ⊤ ↔ (∀ i, |z i| ≤ N) ∧ f z ≠ ⊤ := by
  unfold trunc
  split_ifs with h
  · simp [h]
  · simp [h]

lemma trunc_eq {N : ℤ} {f : (V → ℤ) → WithTop ℝ} {z : V → ℤ} (h : ∀ i, |z i| ≤ N) :
    trunc N f z = f z := by
  unfold trunc; rw [if_pos h]

lemma trunc_val {N : ℤ} {f : (V → ℤ) → WithTop ℝ} {z : V → ℤ} {a : ℝ}
    (h : trunc N f z = (a : WithTop ℝ)) : f z = (a : WithTop ℝ) := by
  unfold trunc at h
  split_ifs at h with hb
  · exact h
  · exact absurd h WithTop.top_ne_coe

lemma trunc_intval (N : ℤ) {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) :
    IsIntegerValued (trunc N f) := by
  intro z
  unfold trunc
  split_ifs with h
  · exact hZ z
  · exact Or.inl rfl

lemma trunc_mexc (N : ℤ) {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) :
    MExchangeAxiom (trunc N f) := by
  intro x hx y hy u hu
  obtain ⟨hbx, hx'⟩ := trunc_ne_top.1 hx
  obtain ⟨hby, hy'⟩ := trunc_ne_top.1 hy
  obtain ⟨v, hv, h⟩ := hf x hx' y hy' u hu
  have hu' : y u < x u := (Finset.mem_filter.1 hu).2
  have hv' : x v < y v := (Finset.mem_filter.1 hv).2
  refine ⟨v, hv, ?_⟩
  have hbx' : ∀ i, -N ≤ x i ∧ x i ≤ N := fun i => abs_le.1 (hbx i)
  have hby' : ∀ i, -N ≤ y i ∧ y i ≤ N := fun i => abs_le.1 (hby i)
  have b1 : ∀ i, |x i - CharVec u i + CharVec v i| ≤ N := by
    intro i
    apply abs_le.2
    have := hbx' i; have := hby' i; have := hbx' u; have := hby' u
    have := hbx' v; have := hby' v
    simp only [CharVec]
    split_ifs with h1 h2 h2 <;> subst_vars <;> omega
  have b2 : ∀ i, |y i + CharVec u i - CharVec v i| ≤ N := by
    intro i
    apply abs_le.2
    have := hbx' i; have := hby' i; have := hbx' u; have := hby' u
    have := hbx' v; have := hby' v
    simp only [CharVec]
    split_ifs with h1 h2 h2 <;> subst_vars <;> omega
  rw [trunc_eq hbx, trunc_eq hby, trunc_eq b1, trunc_eq b2]
  exact h

lemma box_finite (N : ℤ) : {z : V → ℤ | ∀ i, |z i| ≤ N}.Finite := by
  have : {z : V → ℤ | ∀ i, |z i| ≤ N} = Set.pi Set.univ (fun _ => Set.Icc (-N) N) := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
  rw [this]
  exact Set.Finite.pi fun _ => Set.finite_Icc _ _

lemma trunc_conj_ne_top {N : ℤ} {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f)
    (hne : ∃ z, trunc N f z ≠ ⊤) (p : V → ℤ) : ConvexConjugate (trunc N f) p ≠ ⊤ := by
  obtain ⟨B, hB⟩ := ((box_finite (V := V) N).image
    (fun z => idot p z - iv (trunc N f) z)).bddAbove
  apply cc_ne_top_of_bdd (trunc_intval N hZ) hne B
  intro y hy
  exact hB ⟨y, (trunc_ne_top.1 hy).1, rfl⟩

lemma trunc_conj_le {N : ℤ} {f : (V → ℤ) → WithTop ℝ} {p : V → ℤ} {A : ℝ}
    (hA : ConvexConjugate f p = ((A : ℝ) : WithTop ℝ)) (hne : ∃ z, trunc N f z ≠ ⊤) :
    ConvexConjugate (trunc N f) p ≤ ((A : ℝ) : WithTop ℝ) :=
  cc_le hne fun z a ha => cc_bdd hA (trunc_val ha)

lemma trunc_approx {N : ℤ} {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) {z : V → ℤ}
    (hz : f z ≠ ⊤) (hb : ∀ i, |z i| ≤ N) (p : V → ℤ) :
    ((((idot p z - iv f z : ℤ)) : ℝ) : WithTop ℝ) ≤ ConvexConjugate (trunc N f) p := by
  have h : trunc N f z = (((iv f z : ℤ) : ℝ) : WithTop ℝ) := by
    rw [trunc_eq hb]; exact iv_spec hZ hz
  have := cc_ge h p
  rw [dot_eq] at this
  exact_mod_cast this

lemma abs_le_sum3 (a b c : V → ℤ) (i : V) :
    |a i| ≤ ∑ j, (|a j| + |b j| + |c j|) ∧ |b i| ≤ ∑ j, (|a j| + |b j| + |c j|) ∧
      |c i| ≤ ∑ j, (|a j| + |b j| + |c j|) := by
  have h := Finset.single_le_sum (f := fun j => |a j| + |b j| + |c j|)
    (fun j _ => by positivity) (Finset.mem_univ i)
  have := abs_nonneg (a i); have := abs_nonneg (b i); have := abs_nonneg (c i)
  refine ⟨by linarith, by linarith, by linarith⟩

theorem mconv_sbf {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f) :
    SBF (ConvexConjugate f) := by
  intro p q
  rw [ge_iff_le]
  by_cases hne : ∃ y, f y ≠ ⊤
  swap
  · push Not at hne
    rw [cc_empty hne p, top_add]; exact le_top
  by_cases hp : ConvexConjugate f p = ⊤
  · rw [hp, top_add]; exact le_top
  by_cases hq : ConvexConjugate f q = ⊤
  · rw [hq, add_top]; exact le_top
  obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.1 hp
  obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.1 hq
  obtain ⟨y0, hy0⟩ := hne
  have key : ∀ N : ℤ, (∀ i, |y0 i| ≤ N) →
      ConvexConjugate (trunc N f) (p ⊔ q) + ConvexConjugate (trunc N f) (p ⊓ q) ≤
        ((A + B : ℝ) : WithTop ℝ) := by
    intro N hN
    have hfN := trunc_mexc N hf
    have hZN := trunc_intval N hZ
    have hneN : ∃ z, trunc N f z ≠ ⊤ := ⟨y0, trunc_ne_top.2 ⟨hN, hy0⟩⟩
    have hfin : ∀ r, ConvexConjugate (trunc N f) r ≠ ⊤ := fun r => trunc_conj_ne_top hZ hneN r
    have hG : ∀ r, ConvexConjugate (trunc N f) r =
        (((iv (ConvexConjugate (trunc N f)) r : ℤ) : ℝ) : WithTop ℝ) :=
      fun r => iv_spec (conj_intval hZN) (hfin r)
    have hloc : ∀ r u v, u ≠ v →
        iv (ConvexConjugate (trunc N f)) r +
          iv (ConvexConjugate (trunc N f)) (r + CharVec u + CharVec v) ≤
        iv (ConvexConjugate (trunc N f)) (r + CharVec u) +
          iv (ConvexConjugate (trunc N f)) (r + CharVec v) := by
      intro r u v huv
      obtain ⟨x, hx⟩ := cc_attain hZN hneN (hfin (r + CharVec u + CharVec v))
      obtain ⟨y, hy⟩ := cc_attain hZN hneN (hfin r)
      have := local_sbf hfN hZN huv hx hy
      rw [hG, hG, hG, hG, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at this
      exact_mod_cast this
    have hl := lattice_sbf _ hloc p q
    have h1 := trunc_conj_le hA.symm hneN
    have h2 := trunc_conj_le hB.symm hneN
    rw [hG] at h1 h2
    rw [WithTop.coe_le_coe] at h1 h2
    rw [hG, hG, ← WithTop.coe_add, WithTop.coe_le_coe]
    have : (((iv (ConvexConjugate (trunc N f)) (p ⊔ q) +
        iv (ConvexConjugate (trunc N f)) (p ⊓ q) : ℤ)) : ℝ) ≤
        (((iv (ConvexConjugate (trunc N f)) p + iv (ConvexConjugate (trunc N f)) q : ℤ)) : ℝ) := by
      exact_mod_cast hl
    push_cast at this
    linarith
  -- finiteness of the two right-hand conjugates
  have fin1 : ∀ r s : V → ℤ, (r = p ⊔ q ∧ s = p ⊓ q) ∨ (r = p ⊓ q ∧ s = p ⊔ q) →
      ConvexConjugate f r ≠ ⊤ := by
    intro r s hrs
    apply cc_ne_top_of_bdd hZ ⟨y0, hy0⟩ (⌈A + B⌉ - (idot s y0 - iv f y0))
    intro z hz
    have hb := fun i => abs_le_sum3 z y0 y0 i
    have hk := key _ (fun i => (hb i).2.1)
    have h1 := trunc_approx (N := ∑ j, (|z j| + |y0 j| + |y0 j|)) hZ hz (fun i => (hb i).1) r
    have h2 := trunc_approx (N := ∑ j, (|z j| + |y0 j| + |y0 j|)) hZ hy0 (fun i => (hb i).2.1) s
    have h3 : ((((idot r z - iv f z : ℤ)) : ℝ) : WithTop ℝ) + ((((idot s y0 - iv f y0 : ℤ)) : ℝ) : WithTop ℝ) ≤
        ((A + B : ℝ) : WithTop ℝ) := by
      rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (add_le_add h1 h2).trans hk
      · exact (add_le_add h1 h2).trans (by rw [add_comm]; exact hk)
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h3
    have h4 : A + B ≤ ((⌈A + B⌉ : ℤ) : ℝ) := Int.le_ceil _
    have : ((idot r z - iv f z : ℤ) : ℝ) ≤ ((⌈A + B⌉ - (idot s y0 - iv f y0) : ℤ) : ℝ) := by
      push_cast at h3 ⊢; linarith
    exact_mod_cast this
  obtain ⟨x1, hx1⟩ := cc_attain hZ ⟨y0, hy0⟩ (fin1 (p ⊔ q) (p ⊓ q) (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨x2, hx2⟩ := cc_attain hZ ⟨y0, hy0⟩ (fin1 (p ⊓ q) (p ⊔ q) (Or.inr ⟨rfl, rfl⟩))
  have hb := fun i => abs_le_sum3 x1 x2 y0 i
  have hk := key _ (fun i => (hb i).2.2)
  have h1 := trunc_approx (N := ∑ j, (|x1 j| + |x2 j| + |y0 j|)) hZ hx1.1 (fun i => (hb i).1) (p ⊔ q)
  have h2 := trunc_approx (N := ∑ j, (|x1 j| + |x2 j| + |y0 j|)) hZ hx2.1 (fun i => (hb i).2.1) (p ⊓ q)
  rw [cc_of_max hZ hx1, cc_of_max hZ hx2, ← hA, ← hB, ← WithTop.coe_add]
  exact (add_le_add h1 h2).trans hk

theorem mconv_lconv {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f) (hZ : IsIntegerValued f) :
    SBF (ConvexConjugate f) ∧ TRF (ConvexConjugate f) :=
  ⟨mconv_sbf hf hZ, mconv_trf hf hZ⟩

end D

/-! ## E. L-side: DC-3 (conjugate of L is M) and DC-4 (L biconjugacy) -/

section GreedyCopy
open Finset

/-- Greedy on a ring family (copied from our proved sibling 7d18bedc, integer version). -/
theorem greedyZ {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (W : Finset α), W.card ≤ n → ∀ (D : Set (Finset α)) (ρ : Finset α → ℤ)
      (C : Set (Finset α)), (∀ X ∈ D, X ⊆ W) → ∅ ∈ D → W ∈ D →
      (∀ X ∈ D, ∀ Y ∈ D, X ∪ Y ∈ D ∧ X ∩ Y ∈ D) →
      (∀ X ∈ D, ∀ Y ∈ D, ρ (X ∪ Y) + ρ (X ∩ Y) ≤ ρ X + ρ Y) → ρ ∅ = 0 →
      C ⊆ D → IsChain (· ⊆ ·) C →
      ∃ μ : α → ℤ, (∀ X ∈ D, ∑ a ∈ X, μ a ≤ ρ X) ∧ (∀ X ∈ C, ∑ a ∈ X, μ a = ρ X) ∧
        ∑ a ∈ W, μ a = ρ W := by
  intro n
  induction n with
  | zero =>
    intro W hW D ρ C hDW _ _ _ _ hρ0 hCD _
    have hW0 : W = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hW)
    subst hW0
    refine ⟨0, ?_, ?_, ?_⟩
    · intro X hX; rw [Finset.subset_empty.mp (hDW X hX)]; simp [hρ0]
    · intro X hX; rw [Finset.subset_empty.mp (hDW X (hCD hX))]; simp [hρ0]
    · simp [hρ0]
  | succ n ih =>
    intro W hW D ρ C hDW hD0 hDW' hDcl hsub hρ0 hCD hC
    by_cases hWe : W = ∅
    · subst hWe
      refine ⟨0, ?_, ?_, ?_⟩
      · intro X hX; rw [Finset.subset_empty.mp (hDW X hX)]; simp [hρ0]
      · intro X hX; rw [Finset.subset_empty.mp (hDW X (hCD hX))]; simp [hρ0]
      · simp [hρ0]
    have hWne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWe
    -- B : a smallest member of {X ∈ C nonempty} ∪ {W}
    set K : Set (Finset α) := {X | (X ∈ C ∧ X.Nonempty) ∨ X = W} with hK
    have hKfin : K.Finite := by
      apply (W.powerset.finite_toSet).subset
      intro X hX
      rcases hX with ⟨hXC, -⟩ | rfl
      · exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hDW X (hCD hXC)))
      · exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr le_rfl)
    obtain ⟨B, hBK, hBmin⟩ := Set.exists_min_image K Finset.card hKfin ⟨W, Or.inr rfl⟩
    have hBD : B ∈ D := by
      rcases hBK with ⟨hBC, -⟩ | rfl
      · exact hCD hBC
      · exact hDW'
    have hBne : B.Nonempty := by
      rcases hBK with ⟨-, h⟩ | rfl
      · exact h
      · exact hWne
    have hBsub : ∀ X ∈ C, X.Nonempty → B ⊆ X := by
      intro X hXC hXne
      have hXK : X ∈ K := Or.inl ⟨hXC, hXne⟩
      have hcard := hBmin X hXK
      rcases hBK with ⟨hBC, -⟩ | rfl
      · by_cases hXB : X = B
        · rw [hXB]
        · rcases hC hXC hBC hXB with h | h
          · exact (Finset.eq_of_subset_of_card_le h hcard) ▸ le_rfl
          · exact h
      · have hXW : X ⊆ B := hDW X (hCD hXC)
        exact (Finset.eq_of_subset_of_card_le hXW hcard) ▸ le_rfl
    -- A : a minimal nonempty member of D inside B
    set Aset : Set (Finset α) := {X | X ∈ D ∧ X.Nonempty ∧ X ⊆ B} with hAset
    have hAfin : Aset.Finite := by
      apply (B.powerset.finite_toSet).subset
      intro X hX
      exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr hX.2.2)
    obtain ⟨A, ⟨hAD, hAne, hAB⟩, hAmin⟩ :=
      Set.exists_min_image Aset Finset.card hAfin ⟨B, hBD, hBne, le_rfl⟩
    have hAW : A ⊆ W := hDW A hAD
    have hAdich : ∀ X ∈ D, X ∩ A = ∅ ∨ A ⊆ X := by
      intro X hX
      by_cases h : (X ∩ A).Nonempty
      · right
        have hmem : X ∩ A ∈ Aset :=
          ⟨(hDcl X hX A hAD).2, h, (Finset.inter_subset_right).trans hAB⟩
        have hc := hAmin _ hmem
        have heq := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := X)) hc
        rw [← heq]; exact Finset.inter_subset_left
      · left; exact Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨a0, ha0⟩ := hAne
    -- recursion
    set W' := W \ A with hW'
    have hW'card : W'.card ≤ n := by
      have h1 : W'.card < W.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro h
        have := h (hAW ha0)
        simp [hW'] at this
        exact this.2 ha0
      omega
    set D' : Set (Finset α) := {Y | Y ⊆ W' ∧ Y ∪ A ∈ D} with hD'
    set ρ' : Finset α → ℤ := fun Y => ρ (Y ∪ A) - ρ A with hρ'
    set C' : Set (Finset α) := {Y | Y ⊆ W' ∧ Y ∪ A ∈ C} with hC'
    have eU : ∀ Y1 Y2 : Finset α, (Y1 ∪ Y2) ∪ A = (Y1 ∪ A) ∪ (Y2 ∪ A) := by
      intro Y1 Y2; ext a; simp only [Finset.mem_union]; tauto
    have eI : ∀ Y1 Y2 : Finset α, (Y1 ∩ Y2) ∪ A = (Y1 ∪ A) ∩ (Y2 ∪ A) := by
      intro Y1 Y2; ext a; simp only [Finset.mem_union, Finset.mem_inter]; tauto
    have hdisj : ∀ Y ⊆ W', Disjoint Y A := by
      intro Y hY
      rw [Finset.disjoint_left]
      intro a ha haA
      have := hY ha
      simp [hW'] at this
      exact this.2 haA
    have hrec : ∀ Y ⊆ W', (Y ∪ A) \ A = Y := by
      intro Y hY
      rw [Finset.union_sdiff_right]
      exact Finset.sdiff_eq_self_of_disjoint (hdisj Y hY)
    obtain ⟨μ', hμ'D, hμ'C, hμ'W⟩ := ih W' hW'card D' ρ' C'
      (fun X hX => hX.1)
      ⟨Finset.empty_subset _, by simpa using hAD⟩
      ⟨le_rfl, by rw [hW', Finset.sdiff_union_of_subset hAW]; exact hDW'⟩
      (by
        intro X hX Y hY
        refine ⟨⟨Finset.union_subset hX.1 hY.1, ?_⟩, ⟨(Finset.inter_subset_left).trans hX.1, ?_⟩⟩
        · rw [eU]; exact (hDcl _ hX.2 _ hY.2).1
        · rw [eI]; exact (hDcl _ hX.2 _ hY.2).2)
      (by
        intro X hX Y hY
        simp only [hρ']
        rw [eU, eI]
        have := hsub _ hX.2 _ hY.2
        linarith)
      (by simp [hρ'])
      (fun X hX => ⟨hX.1, hCD hX.2⟩)
      (by
        intro X hX Y hY hXY
        have hne : X ∪ A ≠ Y ∪ A := by
          intro h
          apply hXY
          rw [← hrec X hX.1, ← hrec Y hY.1, h]
        rcases hC hX.2 hY.2 hne with h | h
        · left
          intro a ha
          have := h (Finset.mem_union_left A ha)
          rcases Finset.mem_union.mp this with h1 | h1
          · exact h1
          · exact absurd h1 (Finset.disjoint_left.mp (hdisj X hX.1) ha)
        · right
          intro a ha
          have := h (Finset.mem_union_left A ha)
          rcases Finset.mem_union.mp this with h1 | h1
          · exact h1
          · exact absurd h1 (Finset.disjoint_left.mp (hdisj Y hY.1) ha))
    set μ : α → ℤ := fun a => if a ∈ A then (if a = a0 then ρ A else 0) else μ' a with hμ
    have hsplit : ∀ X : Finset α, ∑ a ∈ X, μ a = ∑ a ∈ X ∩ A, μ a + ∑ a ∈ X \ A, μ' a := by
      intro X
      rw [← Finset.sum_inter_add_sum_sdiff X A μ]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have : a ∉ A := (Finset.mem_sdiff.mp ha).2
      simp [hμ, this]
    have hAsum : ∑ a ∈ A, μ a = ρ A := by
      rw [Finset.sum_congr rfl (g := fun a => if a = a0 then ρ A else 0)]
      · rw [Finset.sum_ite_eq' A a0]; simp [ha0]
      · intro a ha; simp [hμ, ha]
    have hfull : ∀ X, A ⊆ X → X \ A ⊆ W' → (X \ A) ∪ A = X := by
      intro X hAX _
      exact Finset.sdiff_union_of_subset hAX
    refine ⟨μ, ?_, ?_, ?_⟩
    · intro X hX
      have hXW := hDW X hX
      have hXA' : X \ A ∈ D' := by
        refine ⟨Finset.sdiff_subset_sdiff hXW le_rfl, ?_⟩
        rw [Finset.sdiff_union_self_eq_union]
        exact (hDcl X hX A hAD).1
      have h1 := hμ'D _ hXA'
      simp only [hρ', Finset.sdiff_union_self_eq_union] at h1
      rw [hsplit]
      rcases hAdich X hX with h | h
      · rw [h, Finset.sum_empty, zero_add]
        have := hsub X hX A hAD
        rw [h, hρ0] at this
        linarith
      · rw [Finset.inter_eq_right.mpr h, hAsum]
        rw [Finset.union_eq_left.mpr h] at h1
        linarith
    · intro X hX
      by_cases hXe : X.Nonempty
      · have hAX : A ⊆ X := hAB.trans (hBsub X hX hXe)
        have hXW := hDW X (hCD hX)
        have hmem : X \ A ∈ C' := by
          refine ⟨Finset.sdiff_subset_sdiff hXW le_rfl, ?_⟩
          rw [Finset.sdiff_union_of_subset hAX]; exact hX
        have h1 := hμ'C _ hmem
        simp only [hρ', Finset.sdiff_union_of_subset hAX] at h1
        rw [hsplit, Finset.inter_eq_right.mpr hAX, hAsum, h1]
        ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hXe]; simp [hρ0]
    · simp only [hρ', hW', Finset.sdiff_union_of_subset hAW] at hμ'W
      rw [hsplit, Finset.inter_eq_right.mpr hAW, hAsum, hμ'W]
      ring

/-- L-optimality criterion (copied verbatim from our proved sibling 7d18bedc). -/
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
  have hk : G y = G y0 ∨ True := Or.inr trivial
  clear hk
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

end GreedyCopy

section E
variable {V : Type*} [Fintype V] [DecidableEq V]

def cst (c : ℤ) : V → ℤ := fun _ => c

def chi (X : Finset V) : V → ℤ := fun a => if a ∈ X then 1 else 0

lemma idot_sub_left (p q x : V → ℤ) : idot (p - q) x = idot p x - idot q x := by
  simp only [idot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma idot_cst (x : V → ℤ) (c : ℤ) : idot x (cst c) = c * ∑ i, x i := by
  simp only [idot, cst, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma idot_one_right (x : V → ℤ) : idot x (1 : V → ℤ) = ∑ i, x i := by
  simp [idot]

lemma idot_chi (x : V → ℤ) (X : Finset V) : idot x (chi X) = ∑ a ∈ X, x a := by
  simp only [idot, chi, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma idot_ex_left (z q : V → ℤ) (a b : V) : idot (ex z a b) q = idot z q - q a + q b := by
  rw [idot_comm, idot_ex, idot_comm]

lemma sum_ex (z : V → ℤ) (a b : V) : ∑ i, ex z a b i = ∑ i, z i := by
  have := idot_ex (1 : V → ℤ) z a b
  rw [idot_one_left, idot_one_left] at this
  simpa using this

lemma idot_sup_inf (x p q : V → ℤ) : idot x (p ⊔ q) + idot x (p ⊓ q) = idot x p + idot x q := by
  simp only [idot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sup_apply, Pi.inf_apply]
  rcases le_total (p i) (q i) with h | h
  · rw [sup_eq_right.2 h, inf_eq_left.2 h]; ring
  · rw [sup_eq_left.2 h, inf_eq_right.2 h]

lemma trf_int {g : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued g) (ht : TRF g)
    (hne : ∃ p, g p ≠ ⊤) : ∃ r : ℤ, ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ) := by
  obtain ⟨r, hr⟩ := ht
  obtain ⟨p0, hp0⟩ := hne
  have h1 := hr p0
  have hp1 : g (p0 + 1) ≠ ⊤ := by
    rw [h1]; exact WithTop.add_ne_top.2 ⟨hp0, WithTop.coe_ne_top⟩
  refine ⟨iv g (p0 + 1) - iv g p0, fun p => ?_⟩
  rw [hr p]
  congr 1
  rw [iv_spec hZ hp1, iv_spec hZ hp0, ← WithTop.coe_add] at h1
  have h2 := WithTop.coe_injective h1
  push_cast
  congr 1
  linarith

lemma shift_cst {g : (V → ℤ) → WithTop ℝ} {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) :
    ∀ (c : ℤ) (p : V → ℤ), g (p + cst c) = g p + ((((c * r : ℤ)) : ℝ) : WithTop ℝ) := by
  have up : ∀ c : ℤ, (∀ p : V → ℤ, g (p + cst c) = g p + ((((c * r : ℤ)) : ℝ) : WithTop ℝ)) →
      ∀ p : V → ℤ, g (p + cst (c + 1)) = g p + (((((c + 1) * r : ℤ)) : ℝ) : WithTop ℝ) := by
    intro c ih p
    have e : p + cst (c + 1) = (p + cst c) + 1 := by funext i; simp [cst]; ring
    rw [e, hr, ih, add_assoc, ← WithTop.coe_add]
    congr 2; push_cast; ring
  have down : ∀ c : ℤ, (∀ p : V → ℤ, g (p + cst c) = g p + ((((c * r : ℤ)) : ℝ) : WithTop ℝ)) →
      ∀ p : V → ℤ, g (p + cst (c - 1)) = g p + (((((c - 1) * r : ℤ)) : ℝ) : WithTop ℝ) := by
    intro c ih p
    have e : p + cst c = (p + cst (c - 1)) + 1 := by funext i; simp [cst]; ring
    have h := ih p
    rw [e, hr] at h
    have h2 := congrArg (fun t => t + (((-r : ℤ) : ℝ) : WithTop ℝ)) h
    rw [add_assoc, ← WithTop.coe_add, add_assoc, ← WithTop.coe_add] at h2
    have e1 : ((r : ℤ) : ℝ) + ((-r : ℤ) : ℝ) = 0 := by push_cast; ring
    rw [e1, WithTop.coe_zero, add_zero] at h2
    rw [h2]
    congr 2; push_cast; ring
  intro c
  induction c using Int.induction_on with
  | zero => intro p; have : p + cst 0 = p := by funext i; simp [cst]
            rw [this]; simp
  | succ n ih => exact up _ ih
  | pred n ih => exact down _ ih

lemma iv_shift {g : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) {p : V → ℤ} (hp : g p ≠ ⊤)
    (c : ℤ) : g (p + cst c) ≠ ⊤ ∧ iv g (p + cst c) = iv g p + c * r := by
  have h := shift_cst hr c p
  have h1 : g (p + cst c) ≠ ⊤ := by rw [h]; exact WithTop.add_ne_top.2 ⟨hp, WithTop.coe_ne_top⟩
  refine ⟨h1, ?_⟩
  rw [iv_spec hZ h1, iv_spec hZ hp, ← WithTop.coe_add] at h
  have := WithTop.coe_injective h
  exact_mod_cast this

lemma sbf_fin {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {p q : V → ℤ}
    (hp : g p ≠ ⊤) (hq : g q ≠ ⊤) :
    g (p ⊔ q) ≠ ⊤ ∧ g (p ⊓ q) ≠ ⊤ ∧ iv g (p ⊔ q) + iv g (p ⊓ q) ≤ iv g p + iv g q := by
  have h := hs p q
  rw [iv_spec hZ hp, iv_spec hZ hq, ← WithTop.coe_add, ge_iff_le] at h
  obtain ⟨h1, h2⟩ := wt_sum_ne_top h
  refine ⟨h1, h2, ?_⟩
  rw [iv_spec hZ h1, iv_spec hZ h2, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  exact_mod_cast h

lemma maxP_lat {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {x p1 p2 : V → ℤ}
    (h1 : IsMaxZ g x p1) (h2 : IsMaxZ g x p2) : IsMaxZ g x (p1 ⊔ p2) ∧ IsMaxZ g x (p1 ⊓ p2) := by
  obtain ⟨f1, f2, hle⟩ := sbf_fin hs hZ h1.1 h2.1
  have a1 := h1.2 _ f1
  have a2 := h1.2 _ f2
  have a3 := h1.2 _ h2.1
  have a4 := h2.2 _ h1.1
  have e := idot_sup_inf x p1 p2
  exact ⟨⟨f1, fun q hq => by have := h1.2 q hq; linarith⟩,
    ⟨f2, fun q hq => by have := h1.2 q hq; linarith⟩⟩

lemma maxP_shift {g : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) {x p : V → ℤ}
    (hx : ∑ i, x i = r) (hp : IsMaxZ g x p) (c : ℤ) : IsMaxZ g x (p + cst c) := by
  obtain ⟨h1, h2⟩ := iv_shift hZ hr hp.1 c
  refine ⟨h1, fun q hq => ?_⟩
  rw [idot_add_right, idot_cst, h2, hx]
  have := hp.2 q hq
  linarith

lemma conj_dom_sum {g : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) (hne : ∃ p, g p ≠ ⊤)
    {x : V → ℤ} (hx : ConvexConjugate g x ≠ ⊤) : ∑ i, x i = r := by
  obtain ⟨p, hp⟩ := cc_attain hZ hne hx
  have t1 := iv_shift hZ hr hp.1 1
  have t2 := iv_shift hZ hr hp.1 (-1)
  have c1 := hp.2 _ t1.1
  have c2 := hp.2 _ t2.1
  rw [idot_add_right, idot_cst, t1.2] at c1
  rw [idot_add_right, idot_cst, t2.2] at c2
  linarith

lemma mono_ineq {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g)
    {x y p q : V → ℤ} (hp : IsMaxZ g x p) (hq : IsMaxZ g y q) :
    ∑ w, (x w - y w) * max (q w - p w) 0 ≤ 0 := by
  obtain ⟨f1, f2, hle⟩ := sbf_fin hs hZ hp.1 hq.1
  have a1 := hp.2 _ f1
  have a2 := hq.2 _ f2
  have e : ∑ w, (x w - y w) * max (q w - p w) 0 =
      (idot x (p ⊔ q) - idot x p) + (idot y (p ⊓ q) - idot y q) := by
    simp only [idot, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Pi.sup_apply, Pi.inf_apply]
    rcases le_total (p w) (q w) with h | h
    · rw [sup_eq_right.2 h, inf_eq_left.2 h, max_eq_left (by linarith)]; ring
    · rw [sup_eq_left.2 h, inf_eq_right.2 h, max_eq_right (by linarith)]; ring
  rw [e]
  linarith

lemma exists_good_w {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) {x y p q : V → ℤ}
    (hsy : ∑ i, y i = r) (hp : IsMaxZ g x p) (hq : IsMaxZ g y q) {u : V} (hu : y u < x u) :
    ∃ w, x w < y w ∧ q u - p u ≤ q w - p w := by
  by_contra hc
  push Not at hc
  have hq' := maxP_shift hZ hr hsy hq (p u - q u + 1)
  have hm := mono_ineq hs hZ hp hq'
  have hqq : ∀ w, (q + cst (V := V) (p u - q u + 1)) w = q w + (p u - q u + 1) := fun w => rfl
  have hterm : ∀ w, 0 ≤ (x w - y w) * max ((q + cst (V := V) (p u - q u + 1)) w - p w) 0 := by
    intro w
    rw [hqq]
    by_cases hw : x w < y w
    · have := hc w hw
      rw [max_eq_right (by linarith)]; simp
    · exact mul_nonneg (by linarith) (le_max_right _ _)
  have hu' : 0 < (x u - y u) * max ((q + cst (V := V) (p u - q u + 1)) u - p u) 0 := by
    rw [hqq, max_eq_left (by linarith)]
    nlinarith
  have := Finset.single_le_sum
    (f := fun w => (x w - y w) * max ((q + cst (V := V) (p u - q u + 1)) w - p w) 0)
    (fun w _ => hterm w) (Finset.mem_univ u)
  linarith

lemma uniform_v {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) {x y : V → ℤ}
    (hsx : ∑ i, x i = r) (hsy : ∑ i, y i = r) {u : V} (hu : y u < x u)
    {p0 q0 : V → ℤ} (hp0 : IsMaxZ g x p0) (hq0 : IsMaxZ g y q0) :
    ∃ v, x v < y v ∧ ∀ p q, IsMaxZ g x p → IsMaxZ g y q → p v - p u ≤ q v - q u := by
  classical
  by_contra H
  push Not at H
  choose! pv qv hpv hqv hlt using H
  let N : Finset V := Finset.univ.filter (fun v => x v < y v)
  have hN : N.Nonempty := by
    obtain ⟨w, hw, -⟩ := exists_good_w hs hZ hr hsy hp0 hq0 hu
    exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩⟩
  have hmN : ∀ v ∈ N, x v < y v := fun v hv => (Finset.mem_filter.1 hv).2
  let pt : V → V → ℤ := fun v => pv v + cst (-(pv v u))
  let qt : V → V → ℤ := fun v => qv v + cst (-(qv v u))
  have hpt : ∀ v ∈ N, IsMaxZ g x (pt v) := fun v hv => maxP_shift hZ hr hsx (hpv v (hmN v hv)) _
  have hqt : ∀ v ∈ N, IsMaxZ g y (qt v) := fun v hv => maxP_shift hZ hr hsy (hqv v (hmN v hv)) _
  let P := N.sup' hN pt
  let Q := N.inf' hN qt
  have hP : IsMaxZ g x P :=
    Finset.sup'_induction (p := IsMaxZ g x) (H := hN) (f := pt)
      (fun a ha b hb => (maxP_lat hs hZ ha hb).1) hpt
  have hQ : IsMaxZ g y Q :=
    Finset.inf'_induction (p := IsMaxZ g y) (H := hN) (f := qt)
      (fun a ha b hb => (maxP_lat hs hZ ha hb).2) hqt
  have hPu : P u = 0 := by
    simp only [P, Finset.sup'_apply]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun v _ => by simp [pt, cst]
    · obtain ⟨v, hv⟩ := hN
      exact le_trans (by simp [pt, cst]) (Finset.le_sup' (fun v => pt v u) hv)
  have hQu : Q u = 0 := by
    simp only [Q, Finset.inf'_apply]
    apply le_antisymm
    · obtain ⟨v, hv⟩ := hN
      exact le_trans (Finset.inf'_le (fun v => qt v u) hv) (by simp [qt, cst])
    · exact Finset.le_inf' _ _ fun v _ => by simp [qt, cst]
  obtain ⟨w, hw, hle⟩ := exists_good_w hs hZ hr hsy hP hQ hu
  have hwN : w ∈ N := Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩
  have h1 : Q w ≤ qt w w := by
    simp only [Q, Finset.inf'_apply]; exact Finset.inf'_le (fun v => qt v w) hwN
  have h2 : pt w w ≤ P w := by
    simp only [P, Finset.sup'_apply]; exact Finset.le_sup' (fun v => pt v w) hwN
  have h3 := hlt w hw
  simp only [pt, qt, Pi.add_apply, cst] at h1 h2
  rw [hPu, hQu] at hle
  linarith

/-- L-optimality wrapper: local optimality in the `+χ_X` directions gives a maximizer. -/
lemma lmax_of_local {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) {z p : V → ℤ}
    (hsz : ∑ i, z i = r) (hp : g p ≠ ⊤)
    (hloc : ∀ X : Finset V, g (p + chi X) ≠ ⊤ →
      idot z (p + chi X) - iv g (p + chi X) ≤ idot z p - iv g p) : IsMaxZ g z p := by
  refine ⟨hp, fun q hq => ?_⟩
  rcases isEmpty_or_nonempty V with hV | hV
  · have : q = p := funext fun a => (IsEmpty.false a).elim
    rw [this]
  let G : (V → ℤ) → WithTop ℝ := fun q => g q + ((((-(idot z q)) : ℤ) : ℝ) : WithTop ℝ)
  have hsub : ∀ a b, G (a ⊔ b) + G (a ⊓ b) ≤ G a + G b := by
    intro a b
    simp only [G]
    rw [add_add_add_comm, add_add_add_comm (g a), ← WithTop.coe_add, ← WithTop.coe_add]
    have e := idot_sup_inf z a b
    have e2 : ((-(idot z (a ⊔ b)) : ℤ) : ℝ) + ((-(idot z (a ⊓ b)) : ℤ) : ℝ) =
        ((-(idot z a) : ℤ) : ℝ) + ((-(idot z b) : ℤ) : ℝ) := by
      push_cast; linarith [(by exact_mod_cast e : ((idot z (a ⊔ b) : ℤ) : ℝ) + ((idot z (a ⊓ b) : ℤ) : ℝ) = ((idot z a : ℤ) : ℝ) + ((idot z b : ℤ) : ℝ))]
    rw [e2]
    exact add_le_add (hs a b) le_rfl
  have htr : ∀ a, G (a + 1) = G a := by
    intro a
    simp only [G]
    rw [hr, idot_add_right, idot_one_right, hsz, add_assoc, ← WithTop.coe_add]
    congr 2; push_cast; ring
  have hGp : G p ≠ ⊤ := WithTop.add_ne_top.2 ⟨hp, WithTop.coe_ne_top⟩
  have hl : ∀ X : Finset V, G p ≤ G (fun a => p a + if a ∈ X then 1 else 0) := by
    intro X
    have e : (fun a => p a + if a ∈ X then (1 : ℤ) else 0) = p + chi X := rfl
    rw [e]
    by_cases hX : g (p + chi X) = ⊤
    · simp only [G, hX, top_add]; exact le_top
    · have := hloc X hX
      simp only [G]
      rw [iv_spec hZ hX, iv_spec hZ hp, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      have : ((idot z (p + chi X) - iv g (p + chi X) : ℤ) : ℝ) ≤ ((idot z p - iv g p : ℤ) : ℝ) := by
        exact_mod_cast this
      push_cast at this ⊢; linarith
  have := loc_glob G hsub htr p hGp hl q
  simp only [G] at this
  rw [iv_spec hZ hq, iv_spec hZ hp, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at this
  have : ((iv g p - idot z p : ℤ) : ℝ) ≤ ((iv g q - idot z q : ℤ) : ℝ) := by
    push_cast at this ⊢; linarith
  have := (Int.cast_le (R := ℝ)).1 this
  linarith

lemma shift_max {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) {z p : V → ℤ} {a b : V}
    (hab : a ≠ b) (hsz : ∑ i, z i = r) (hp : IsMaxZ g z p)
    (hbest : ∀ p', IsMaxZ g z p' → p' b - p' a ≤ p b - p a) : IsMaxZ g (ex z a b) p := by
  apply lmax_of_local hs hZ hr (by rw [sum_ex, hsz]) hp.1
  intro X hX
  rw [idot_ex_left, idot_ex_left]
  have hv := hp.2 _ hX
  simp only [Pi.add_apply, chi]
  by_cases hc : b ∈ X ∧ a ∉ X
  · have hnot : ¬ IsMaxZ g z (p + chi X) := by
      intro hm
      have := hbest _ hm
      simp only [Pi.add_apply, chi, if_pos hc.1, if_neg hc.2] at this
      omega
    have hlt : idot z (p + chi X) - iv g (p + chi X) < idot z p - iv g p := by
      by_contra hc2
      apply hnot
      refine ⟨hX, fun q hq => ?_⟩
      have := hp.2 q hq
      omega
    rw [if_pos hc.1, if_neg hc.2]
    omega
  · have : (if b ∈ X then (1 : ℤ) else 0) ≤ (if a ∈ X then 1 else 0) := by
      split_ifs <;> simp_all
    omega

/-- DC-3: the conjugate of an integer L-convex function is M-convex. -/
theorem lconv_mexc {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (ht : TRF g) (hZ : IsIntegerValued g) :
    MExchangeAxiom (ConvexConjugate g) := by
  intro x hx y hy u hu
  have hx' : ConvexConjugate g x ≠ ⊤ := hx
  have hy' : ConvexConjugate g y ≠ ⊤ := hy
  have hne : ∃ p, g p ≠ ⊤ := by
    by_contra h; push Not at h; exact hx' (cc_empty h x)
  obtain ⟨r, hr⟩ := trf_int hZ ht hne
  have hsx := conj_dom_sum hZ hr hne hx'
  have hsy := conj_dom_sum hZ hr hne hy'
  obtain ⟨p0, hp0⟩ := cc_attain hZ hne hx'
  obtain ⟨q0, hq0⟩ := cc_attain hZ hne hy'
  have hu' : y u < x u := (Finset.mem_filter.1 hu).2
  obtain ⟨v, hv, hgood⟩ := uniform_v hs hZ hr hsx hsy hu' hp0 hq0
  have huv : u ≠ v := by rintro rfl; omega
  obtain ⟨p1, hp1, hbest1⟩ : ∃ p1, IsMaxZ g x p1 ∧
      ∀ p', IsMaxZ g x p' → p' v - p' u ≤ p1 v - p1 u := by
    have hb : ∃ B : ℤ, ∀ n : ℤ, (∃ p', IsMaxZ g x p' ∧ n = p' v - p' u) → n ≤ B :=
      ⟨q0 v - q0 u, by rintro n ⟨p', hp', rfl⟩; exact hgood p' q0 hp' hq0⟩
    obtain ⟨n, ⟨p1, hp1, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hb ⟨_, p0, hp0, rfl⟩
    exact ⟨p1, hp1, fun p' hp' => hmax _ ⟨p', hp', rfl⟩⟩
  obtain ⟨q1, hq1, hbest2⟩ : ∃ q1, IsMaxZ g y q1 ∧
      ∀ q', IsMaxZ g y q' → q' u - q' v ≤ q1 u - q1 v := by
    have hb : ∃ B : ℤ, ∀ n : ℤ, (∃ q', IsMaxZ g y q' ∧ n = q' u - q' v) → n ≤ B :=
      ⟨p0 u - p0 v, by rintro n ⟨q', hq', rfl⟩; have := hgood p0 q' hp0 hq'; linarith⟩
    obtain ⟨n, ⟨q1, hq1, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hb ⟨_, q0, hq0, rfl⟩
    exact ⟨q1, hq1, fun q' hq' => hmax _ ⟨q', hq', rfl⟩⟩
  have h1 := shift_max hs hZ hr huv hsx hp1 hbest1
  have h2 := shift_max hs hZ hr (Ne.symm huv) hsy hq1 hbest2
  refine ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, ?_⟩
  have e : (fun w => y w + CharVec u w - CharVec v w) = ex y v u := by
    funext w; simp only [ex]; ring
  have e2 : (fun w => x w - CharVec u w + CharVec v w) = ex x u v := rfl
  rw [e, e2, cc_of_max hZ hp1, cc_of_max hZ hq1, cc_of_max hZ h1, cc_of_max hZ h2,
    ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe, idot_ex_left,
    idot_ex_left]
  have := hgood p1 q1 hp1 hq1
  have : (((idot x p1 - p1 u + p1 v - iv g p1 + (idot y q1 - q1 v + q1 u - iv g q1)) : ℤ) : ℝ) ≤
      (((idot x p1 - iv g p1 + (idot y q1 - iv g q1)) : ℤ) : ℝ) := by
    exact_mod_cast (by linarith)
  push_cast at this ⊢
  linarith

lemma chi_sup (p : V → ℤ) (X Y : Finset V) : (p + chi X) ⊔ (p + chi Y) = p + chi (X ∪ Y) := by
  funext a
  simp only [Pi.sup_apply, Pi.add_apply, chi, Finset.mem_union]
  split_ifs <;> simp_all

lemma chi_inf (p : V → ℤ) (X Y : Finset V) : (p + chi X) ⊓ (p + chi Y) = p + chi (X ∩ Y) := by
  funext a
  simp only [Pi.inf_apply, Pi.add_apply, chi, Finset.mem_inter]
  split_ifs <;> simp_all

/-- Integer subgradient of an integer L-convex function (greedy). -/
theorem subgrad_L {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) {p : V → ℤ} (hp : g p ≠ ⊤) :
    ∃ x : V → ℤ, IsMaxZ g x p := by
  classical
  have h0 : p + chi (∅ : Finset V) = p := by funext a; simp [chi]
  have h1 : p + chi (Finset.univ : Finset V) = p + 1 := by funext a; simp [chi]
  have hp1 : g (p + 1) ≠ ⊤ := by rw [hr]; exact WithTop.add_ne_top.2 ⟨hp, WithTop.coe_ne_top⟩
  have hiv1 : iv g (p + 1) = iv g p + r := by
    have h := hr p
    rw [iv_spec hZ hp1, iv_spec hZ hp, ← WithTop.coe_add] at h
    exact_mod_cast WithTop.coe_injective h
  obtain ⟨μ, hμD, -, hμW⟩ := greedyZ (Finset.univ : Finset V).card Finset.univ le_rfl
    {X | g (p + chi X) ≠ ⊤} (fun X => iv g (p + chi X) - iv g p) ∅
    (fun X _ => Finset.subset_univ X)
    (show g (p + chi ∅) ≠ ⊤ by rw [h0]; exact hp)
    (show g (p + chi Finset.univ) ≠ ⊤ by rw [h1]; exact hp1)
    (by
      intro X hX Y hY
      obtain ⟨f1, f2, -⟩ := sbf_fin hs hZ hX hY
      rw [chi_sup] at f1; rw [chi_inf] at f2
      exact ⟨f1, f2⟩)
    (by
      intro X hX Y hY
      obtain ⟨-, -, hle⟩ := sbf_fin hs hZ hX hY
      rw [chi_sup, chi_inf] at hle
      show iv g (p + chi (X ∪ Y)) - iv g p + (iv g (p + chi (X ∩ Y)) - iv g p) ≤
        iv g (p + chi X) - iv g p + (iv g (p + chi Y) - iv g p)
      linarith)
    (show iv g (p + chi ∅) - iv g p = 0 by rw [h0]; ring)
    (Set.empty_subset _) IsChain.empty
  refine ⟨μ, lmax_of_local hs hZ hr ?_ hp ?_⟩
  · change ∑ a ∈ Finset.univ, μ a = iv g (p + chi Finset.univ) - iv g p at hμW
    rw [h1, hiv1] at hμW; rw [hμW]; ring
  · intro X hX
    have := hμD X hX
    change ∑ a ∈ X, μ a ≤ iv g (p + chi X) - iv g p at this
    rw [idot_add_right, idot_chi]
    linarith

/-- Separation of a point outside the domain of an L-convex function. -/
theorem sep_L {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValued g) {r : ℤ}
    (hr : ∀ p, g (p + 1) = g p + (((r : ℤ) : ℝ) : WithTop ℝ)) (hne : ∃ p, g p ≠ ⊤)
    {q : V → ℤ} (hq : g q = ⊤) : ∃ a b : V, ∀ p, g p ≠ ⊤ → p b - p a < q b - q a := by
  classical
  by_contra H
  push Not at H
  rcases isEmpty_or_nonempty V with hV | hV
  · obtain ⟨p0, hp0⟩ := hne
    have : q = p0 := funext fun a => (IsEmpty.false a).elim
    exact hp0 (this ▸ hq)
  choose w hw hwle using H
  let w' : V → V → V → ℤ := fun a b => w a b + cst (q a - w a b a)
  have hw' : ∀ a b, g (w' a b) ≠ ⊤ := fun a b => (iv_shift hZ hr (hw a b) _).1
  let P : V → V → ℤ := fun a => Finset.univ.sup' Finset.univ_nonempty (w' a)
  have hP : ∀ a, g (P a) ≠ ⊤ := fun a =>
    Finset.sup'_induction (p := fun z => g z ≠ ⊤) (H := Finset.univ_nonempty) (f := w' a)
      (fun x hx y hy => (sbf_fin hs hZ hx hy).1) (fun b _ => hw' a b)
  let Q : V → ℤ := Finset.univ.inf' Finset.univ_nonempty P
  have hQ : g Q ≠ ⊤ :=
    Finset.inf'_induction (p := fun z => g z ≠ ⊤) (H := Finset.univ_nonempty) (f := P)
      (fun x hx y hy => (sbf_fin hs hZ hx hy).2.1) (fun a _ => hP a)
  have hPa : ∀ a, P a a = q a := by
    intro a
    simp only [P, Finset.sup'_apply]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun b _ => by simp [w', cst]
    · exact le_trans (by simp [w', cst]) (Finset.le_sup' (fun b => w' a b a) (Finset.mem_univ a))
  have hPc : ∀ a c, q c ≤ P a c := by
    intro a c
    simp only [P, Finset.sup'_apply]
    refine le_trans ?_ (Finset.le_sup' (fun b => w' a b c) (Finset.mem_univ c))
    have := hwle a c
    simp only [w', Pi.add_apply, cst]
    linarith
  have hQq : Q = q := by
    funext c
    simp only [Q, Finset.inf'_apply]
    apply le_antisymm
    · exact le_trans (Finset.inf'_le (fun a => P a c) (Finset.mem_univ c)) (le_of_eq (hPa c))
    · exact Finset.le_inf' _ _ fun a _ => hPc a c
  exact hQ (hQq ▸ hq)

/-- DC-4: biconjugacy for integer L-convex functions. -/
theorem lconv_biconj {g : (V → ℤ) → WithTop ℝ} (hs : SBF g) (ht : TRF g) (hZ : IsIntegerValued g) :
    ConvexConjugate (ConvexConjugate g) = g := by
  funext q
  by_cases hne : ∃ p, g p ≠ ⊤
  · obtain ⟨r, hr⟩ := trf_int hZ ht hne
    by_cases hq : g q = ⊤
    · rw [hq]
      obtain ⟨a, b, hab⟩ := sep_L hs hZ hr hne hq
      obtain ⟨p0, hp0⟩ := hne
      obtain ⟨x0, hx0⟩ := subgrad_L hs hZ hr hp0
      apply cc_top_of_unbdd
      intro M
      let c : ℤ := idot x0 q - (idot x0 p0 - iv g p0)
      let t : ℤ := max 0 (⌈M⌉ - c)
      have ht0 : 0 ≤ t := le_max_left _ _
      let X : V → ℤ := x0 + t • (CharVec b - CharVec a)
      have hX : ∀ p, idot X p = idot x0 p + t * (p b - p a) := by
        intro p
        simp only [X]
        rw [idot_add_left, idot_smul_left, idot_sub_left, idot_charvec_left, idot_charvec_left]
      let B : ℤ := (idot x0 p0 - iv g p0) + t * (q b - q a - 1)
      have hbd : ∀ p, g p ≠ ⊤ → idot X p - iv g p ≤ B := by
        intro p hp
        rw [hX]
        have h1 := hx0.2 p hp
        have h2 := hab p hp
        have h3 : t * (p b - p a) ≤ t * (q b - q a - 1) :=
          mul_le_mul_of_nonneg_left (by omega) ht0
        simp only [B]; linarith
      have hfin : ConvexConjugate g X ≠ ⊤ := cc_ne_top_of_bdd hZ ⟨p0, hp0⟩ B hbd
      obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.1 hfin
      refine ⟨X, A, hA.symm, ?_⟩
      have hAB : A ≤ ((B : ℤ) : ℝ) := by
        have := cc_le (f := g) (p := X) (C := ((B : ℤ) : ℝ)) ⟨p0, hp0⟩ (by
          intro p a ha
          rw [iv_of_eq hZ ha, dot_eq]
          exact_mod_cast hbd p (by rw [ha]; exact WithTop.coe_ne_top))
        rw [← hA, WithTop.coe_le_coe] at this
        exact this
      have e : (∑ i, (q i : ℝ) * (X i : ℝ)) = ((idot X q : ℤ) : ℝ) := by
        rw [dot_eq, idot_comm]
      rw [e, hX]
      have hge : c + t ≤ idot x0 q + t * (q b - q a) - B := by
        simp only [B, c]; ring_nf; linarith
      have hM : M ≤ ((c + t : ℤ) : ℝ) := by
        have h1 : (⌈M⌉ : ℤ) ≤ c + t := by have := le_max_right 0 (⌈M⌉ - c); omega
        calc M ≤ (⌈M⌉ : ℝ) := Int.le_ceil M
          _ ≤ ((c + t : ℤ) : ℝ) := by exact_mod_cast h1
      have : ((c + t : ℤ) : ℝ) ≤ ((idot x0 q + t * (q b - q a) - B : ℤ) : ℝ) := by
        exact_mod_cast hge
      push_cast at this hM hAB ⊢
      linarith
    · obtain ⟨x, hx⟩ := subgrad_L hs hZ hr hq
      exact biconj_of_max hZ hx
  · push Not at hne
    rw [cc_empty (cc_empty hne) q, hne q]

end E

/-! ## F. DC-6: conjugation exchanges the two lifts -/

section F
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sSup_eq_of {S1 S2 : Set EReal} (h1 : ∀ a ∈ S1, a ≤ sSup S2) (h2 : ∀ b ∈ S2, b ≤ sSup S1) :
    sSup S1 = sSup S2 :=
  le_antisymm (sSup_le h1) (sSup_le h2)

lemma lift_M_conj (f : (V → ℤ) → WithTop ℝ) :
    ConvexConjugate (LiftedFunction f) = LiftedFunctionL (ConvexConjugate f) := by
  funext P
  show ConvexConjugate (LiftedFunction f) P = ConvexConjugate f (fun v => P (some v) - P none)
  rw [cc_unfold, cc_unfold]
  congr 1
  apply sSup_eq_of
  · rintro t ⟨X, rfl⟩
    by_cases hX : X none = -(∑ v : V, X (some v))
    · apply le_sSup
      refine ⟨fun v => X (some v), ?_⟩
      have e1 : LiftedFunction f X = f (fun v => X (some v)) := by
        simp only [LiftedFunction, if_pos hX]
      rw [e1]
      congr 2
      rw [Fintype.sum_option, hX]
      push_cast
      rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    · have e1 : LiftedFunction f X = ⊤ := by simp only [LiftedFunction, if_neg hX]
      rw [term_top e1]; exact bot_le
  · rintro t ⟨x, rfl⟩
    apply le_sSup
    refine ⟨fun o => Option.elim o (-(∑ v, x v)) x, ?_⟩
    have e1 : LiftedFunction f (fun o => Option.elim o (-(∑ v, x v)) x) = f x := by
      simp [LiftedFunction]
    rw [e1]
    congr 2
    rw [Fintype.sum_option]
    simp only [Option.elim]
    push_cast
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring

lemma lift_L_conj (g : (V → ℤ) → WithTop ℝ) (hZ : IsIntegerValued g) :
    ConvexConjugate (LiftedFunctionL g) = LiftedFunction (ConvexConjugate g) := by
  funext X
  by_cases hX : X none = -(∑ v : V, X (some v))
  · have e0 : LiftedFunction (ConvexConjugate g) X = ConvexConjugate g (fun v => X (some v)) := by
      simp only [LiftedFunction, if_pos hX]
    rw [e0, cc_unfold, cc_unfold]
    congr 1
    apply sSup_eq_of
    · rintro t ⟨P, rfl⟩
      apply le_sSup
      refine ⟨fun v => P (some v) - P none, ?_⟩
      show _ = _ - ToEReal (g (fun v => P (some v) - P none))
      congr 2
      rw [Fintype.sum_option, hX]
      push_cast
      rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    · rintro t ⟨p, rfl⟩
      apply le_sSup
      refine ⟨fun o => Option.elim o 0 p, ?_⟩
      show _ = _ - ToEReal (g (fun v => p v - 0))
      have e : (fun v => p v - 0) = p := by funext v; ring
      rw [e]
      congr 2
      rw [Fintype.sum_option]
      simp
  · have e0 : LiftedFunction (ConvexConjugate g) X = ⊤ := by
      simp only [LiftedFunction, if_neg hX]
    rw [e0]
    by_cases hne : ∃ p, g p ≠ ⊤
    · obtain ⟨p0, hp0⟩ := hne
      let s : ℤ := X none + ∑ v, X (some v)
      have hs : s ≠ 0 := by intro h; apply hX; simp only [s] at h; linarith
      let C0 : ℤ := ∑ v, X (some v) * p0 v
      apply cc_top_of_unbdd
      intro M
      let K : ℤ := max 0 (⌈M⌉ - C0 + iv g p0)
      let t : ℤ := s * K
      refine ⟨fun o => Option.elim o t (fun v => p0 v + t), ((iv g p0 : ℤ) : ℝ), ?_, ?_⟩
      · show g (fun v => (p0 v + t) - t) = _
        have e : (fun v => (p0 v + t) - t) = p0 := by funext v; ring
        rw [e]; exact iv_spec hZ hp0
      · have e : (∑ o, (X o : ℝ) * ((Option.elim o t (fun v => p0 v + t) : ℤ) : ℝ)) =
            ((s * t + C0 : ℤ) : ℝ) := by
          rw [Fintype.sum_option]
          simp only [Option.elim, s, C0]
          push_cast
          rw [add_mul, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [e]
        have hK : 0 ≤ K := le_max_left _ _
        have hss : 1 ≤ s * s := by
          rcases lt_or_gt_of_ne hs with h | h <;> nlinarith
        have h1 : K ≤ s * t := by simp only [t]; nlinarith
        have h2 : ⌈M⌉ ≤ s * t + C0 - iv g p0 := by
          have := le_max_right 0 (⌈M⌉ - C0 + iv g p0); simp only [K] at h1; omega
        have h3 : M ≤ ((⌈M⌉ : ℤ) : ℝ) := Int.le_ceil M
        have h4 : ((⌈M⌉ : ℤ) : ℝ) ≤ ((s * t + C0 - iv g p0 : ℤ) : ℝ) := by exact_mod_cast h2
        push_cast at h4 ⊢
        linarith
    · push Not at hne
      exact cc_empty (fun P => hne _) X

theorem conj_lift (V : Type*) [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ,
      ConvexConjugate (LiftedFunction f) = LiftedFunctionL (ConvexConjugate f)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, IsIntegerValued g →
      ConvexConjugate (LiftedFunctionL g) = LiftedFunction (ConvexConjugate g)) :=
  ⟨lift_M_conj, lift_L_conj⟩

theorem lift_intval {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValued f) :
    IsIntegerValued (LiftedFunction f) ∧ IsIntegerValued (LiftedFunctionL f) := by
  constructor
  · intro x; unfold LiftedFunction; split_ifs
    · exact hZ _
    · exact Or.inl rfl
  · intro x; exact hZ _

theorem lift_inj (V : Type*) [Fintype V] :
    Function.Injective (LiftedFunction (V := V)) ∧ Function.Injective (LiftedFunctionL (V := V)) := by
  constructor
  · intro f g h; funext x
    have := congrFun h (fun o => Option.elim o (-(∑ v, x v)) x)
    simpa [LiftedFunction] using this
  · intro f g h; funext x
    have := congrFun h (fun o => Option.elim o 0 x)
    simpa [LiftedFunctionL] using this

end F

end Pd94

open DiscreteConvex.ConjugacyDuality in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, DiscreteConvex.MConvexFunctions.MExchangeAxiom f →
        IsIntegerValued f →
        DiscreteConvex.LConvexFunctions.SBF (ConvexConjugate f) ∧
          DiscreteConvex.LConvexFunctions.TRF (ConvexConjugate f) ∧
          IsIntegerValued (ConvexConjugate f) ∧
          ConvexConjugate (ConvexConjugate f) = f) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, DiscreteConvex.LConvexFunctions.SBF g →
        DiscreteConvex.LConvexFunctions.TRF g → IsIntegerValued g →
        DiscreteConvex.MConvexFunctions.MExchangeAxiom (ConvexConjugate g) ∧
          IsIntegerValued (ConvexConjugate g) ∧
          ConvexConjugate (ConvexConjugate g) = g) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, DiscreteConvex.MConvexFunctions.MNaturalConvex f →
        IsIntegerValued f →
        DiscreteConvex.LConvexFunctions.LNaturalConvex (ConvexConjugate f) ∧
          IsIntegerValued (ConvexConjugate f) ∧
          ConvexConjugate (ConvexConjugate f) = f) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, DiscreteConvex.LConvexFunctions.LNaturalConvex g →
        IsIntegerValued g →
        DiscreteConvex.MConvexFunctions.MNaturalConvex (ConvexConjugate g) ∧
          IsIntegerValued (ConvexConjugate g) ∧
          ConvexConjugate (ConvexConjugate g) = g) := by
  refine ⟨fun f hf hZ => ?_, fun g hs ht hZ => ?_, fun f hf hZ => ?_, fun g hg hZ => ?_⟩
  · exact ⟨Pd94.mconv_sbf hf hZ, Pd94.mconv_trf hf hZ, Pd94.conj_intval hZ,
      Pd94.mconv_biconj hf hZ⟩
  · exact ⟨Pd94.lconv_mexc hs ht hZ, Pd94.conj_intval hZ, Pd94.lconv_biconj hs ht hZ⟩
  · have hZ' := (Pd94.lift_intval hZ).1
    have h1 := Pd94.mconv_lconv hf hZ'
    have h2 := Pd94.mconv_biconj hf hZ'
    rw [(Pd94.conj_lift V).1 f] at h1 h2
    rw [(Pd94.conj_lift V).2 _ (Pd94.conj_intval hZ)] at h2
    exact ⟨h1, Pd94.conj_intval hZ, (Pd94.lift_inj V).1 h2⟩
  · have hZ' := (Pd94.lift_intval hZ).2
    have h1 := Pd94.lconv_mexc hg.1 hg.2 hZ'
    have h2 := Pd94.lconv_biconj hg.1 hg.2 hZ'
    rw [(Pd94.conj_lift V).2 g hZ] at h1 h2
    rw [(Pd94.conj_lift V).1] at h2
    exact ⟨h1, Pd94.conj_intval hZ, (Pd94.lift_inj V).2 h2⟩
