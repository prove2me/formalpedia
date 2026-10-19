-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.Quasi.m_exchange_iff_perturbed_quasi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:30:40.282329+00:00
-- url     : https://prove2.me/submissions/637fe49b-7b94-4052-a2db-c96322970365

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_PerturbedM

open DiscreteConvex.MConvexFunctions DiscreteConvex.MConvexFunctions.Quasi

set_option linter.unusedSectionVars false

namespace MQAux

variable {V : Type*} [Fintype V] [DecidableEq V]

def xm (x : V → ℤ) (u v : V) : V → ℤ := fun w => x w - CharVec u w + CharVec v w
def ym (y : V → ℤ) (u v : V) : V → ℤ := fun w => y w + CharVec u w - CharVec v w
def L (p : V → ℝ) (x : V → ℤ) : ℝ := ∑ v, p v * (x v : ℝ)

def Exch (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) (u v : V) : Prop :=
  f (xm x u v) + f (ym y u v) ≤ f x + f y

lemma sum_char (p : V → ℝ) (u : V) : ∑ w, p w * ((CharVec u w : ℤ) : ℝ) = p u := by
  simp [CharVec]

lemma L_xm (p : V → ℝ) (x : V → ℤ) (u v : V) : L p (xm x u v) = L p x - p u + p v := by
  simp only [L, xm]; push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_char]

lemma L_ym (p : V → ℝ) (x : V → ℤ) (u v : V) : L p (ym x u v) = L p x + p u - p v := by
  simp only [L, ym]; push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_char]

lemma L_Z (p : V → ℝ) (x : V → ℤ) (u u' a b : V) :
    L p (fun w => x w - CharVec u w - CharVec u' w + CharVec a w + CharVec b w)
      = L p x - p u - p u' + p a + p b := by
  simp only [L]; push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_char]

lemma pert_eq (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (x : V → ℤ) :
    PerturbedM f p x = f x + ((-(L p x) : ℝ) : WithTop ℝ) := rfl

lemma pert_ne_top (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (x : V → ℤ) :
    PerturbedM f p x ≠ ⊤ ↔ f x ≠ ⊤ := by
  rw [pert_eq, WithTop.add_ne_top]; simp

lemma pert_comp (f : (V → ℤ) → WithTop ℝ) (p q : V → ℝ) :
    PerturbedM (PerturbedM f p) q = PerturbedM f (p + q) := by
  funext x
  simp only [PerturbedM, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [add_assoc, ← WithTop.coe_add]; congr 2; ring

lemma exch_pert (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (x y : V → ℤ) (u v : V) :
    Exch (PerturbedM f p) x y u v ↔ Exch f x y u v := by
  unfold Exch
  simp only [pert_eq, L_xm, L_ym]
  have e1 : f (xm x u v) + (((-(L p x - p u + p v)) : ℝ) : WithTop ℝ) +
      (f (ym y u v) + (((-(L p y + p u - p v)) : ℝ) : WithTop ℝ))
      = (f (xm x u v) + f (ym y u v)) + (((-(L p x) + -(L p y)) : ℝ) : WithTop ℝ) := by
    rw [show (-(L p x) + -(L p y)) = (-(L p x - p u + p v)) + (-(L p y + p u - p v)) by ring,
      WithTop.coe_add]
    ac_rfl
  have e2 : f x + (((-(L p x)) : ℝ) : WithTop ℝ) + (f y + (((-(L p y)) : ℝ) : WithTop ℝ))
      = (f x + f y) + (((-(L p x) + -(L p y)) : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_add]; ac_rfl
  rw [e1, e2]
  exact WithTop.add_le_add_iff_right (WithTop.coe_ne_top)

lemma sep (r1 r2 : ℝ) (A B : WithTop ℝ) (h : (r1 : WithTop ℝ) + r2 < A + B) :
    ∃ s : ℝ, (r1 : WithTop ℝ) < A + s ∧ (r2 : WithTop ℝ) < B + ((-s : ℝ) : WithTop ℝ) := by
  induction A using WithTop.recTopCoe with
  | top =>
    induction B using WithTop.recTopCoe with
    | top => exact ⟨0, by simp, by simp⟩
    | coe b =>
      refine ⟨b - r2 - 1, by simp, ?_⟩
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]; linarith
  | coe a =>
    induction B using WithTop.recTopCoe with
    | top =>
      refine ⟨r1 - a + 1, ?_, by simp⟩
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]; linarith
    | coe b =>
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe] at h
      refine ⟨r1 - a + (a + b - r1 - r2) / 2, ?_, ?_⟩ <;>
        rw [← WithTop.coe_add, WithTop.coe_lt_coe] <;> linarith

lemma sepP (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) (u : V)
    (W : Finset V) (hfail : ∀ w ∈ W, f x + f y < f (xm x u w) + f (ym y u w)) :
    ∃ s : V → ℝ, ∀ p : V → ℝ, (∀ w ∈ W, p u - p w = s w) → ∀ w ∈ W,
      PerturbedM f p x < PerturbedM f p (xm x u w) ∧
      PerturbedM f p y < PerturbedM f p (ym y u w) := by
  obtain ⟨rx, hrx⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨ry, hry⟩ := WithTop.ne_top_iff_exists.1 hy
  have key : ∀ w, ∃ t : ℝ, w ∈ W → ((rx : WithTop ℝ) < f (xm x u w) + t ∧
      (ry : WithTop ℝ) < f (ym y u w) + ((-t : ℝ) : WithTop ℝ)) := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨t, ht⟩ := sep rx ry _ _ (by rw [hrx, hry]; exact hfail w hw)
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose s hs using key
  refine ⟨s, fun p hp w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hs w hw
  rw [pert_eq, pert_eq, pert_eq, pert_eq, L_xm, L_ym, ← hrx, ← hry]
  constructor
  · rw [show -(L p x - p u + p w) = s w + -(L p x) by rw [← hp w hw]; ring, WithTop.coe_add,
      ← add_assoc]
    exact WithTop.add_lt_add_right WithTop.coe_ne_top h1
  · rw [show -(L p y + p u - p w) = -s w + -(L p y) by rw [← hp w hw]; ring, WithTop.coe_add,
      ← add_assoc]
    exact WithTop.add_lt_add_right WithTop.coe_ne_top h2

def N (x y : V → ℤ) : ℕ := ∑ w, (x w - y w).natAbs

lemma N_ym_lt (x y : V → ℤ) (u v : V) (hu : y u < x u) (hv : x v < y v) :
    N x (ym y u v) < N x y := by
  unfold N ym
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    split_ifs with h1 h2 <;> subst_vars <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [CharVec]
    split_ifs with h1 h2 <;> subst_vars <;> omega

lemma N_xm_lt (x y : V → ℤ) (u v : V) (hu : y u < x u) (hv : x v < y v) :
    N (xm x u v) y < N x y := by
  unfold N xm
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    split_ifs with h1 h2 <;> subst_vars <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [CharVec]
    split_ifs with h1 h2 <;> subst_vars <;> omega

lemma mem_pos {x y : V → ℤ} {w : V} : w ∈ SuppPos x y ↔ y w < x w := by
  simp [SuppPos]

lemma mem_neg {x y : V → ℤ} {w : V} : w ∈ SuppNeg x y ↔ x w < y w := by
  simp [SuppNeg]

end MQAux


namespace MQAux

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma loc_core (g : (V → ℤ) → WithTop ℝ) (X Z : V → ℤ) (hX : g X ≠ ⊤) (hZ : g Z ≠ ⊤)
    (u u' a b : V) (hua : u ≠ a) (hub : u ≠ b) (hu'a : u' ≠ a) (hu'b : u' ≠ b)
    (hZdef : Z = fun w => X w - CharVec u w - CharVec u' w + CharVec a w + CharVec b w)
    (p : V → ℝ) (hq : QMw (PerturbedM g p))
    (ha : ∀ w ∈ ({a, b} : Finset V),
      PerturbedM g p X < PerturbedM g p (xm X u w) ∧ PerturbedM g p Z < PerturbedM g p (ym Z u w))
    (heq : u' = u ∨ PerturbedM g p X = PerturbedM g p Z) : False := by
  have hXZ : X ≠ Z := by
    intro h
    have := congrFun (h.trans hZdef) u
    simp only [CharVec] at this
    rw [if_pos trivial, if_neg hua, if_neg hub] at this
    split_ifs at this <;> omega
  obtain ⟨u'', hu'', v'', hv'', hor⟩ :=
    hq X ((pert_ne_top g p X).2 hX) Z ((pert_ne_top g p Z).2 hZ) hXZ
  rw [mem_pos, hZdef] at hu''
  rw [mem_neg, hZdef] at hv''
  simp only [CharVec] at hu'' hv''
  have hu2 : u'' = u ∨ u'' = u' := by
    by_contra hc; push Not at hc
    rw [if_neg hc.1, if_neg hc.2] at hu''
    split_ifs at hu'' <;> omega
  have hv2 : v'' ∈ ({a, b} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc; push Not at hc
    rw [if_neg hc.1, if_neg hc.2] at hv''
    split_ifs at hv'' <;> omega
  rcases hu2 with rfl | rfl
  · rcases hor with h | h
    · exact absurd h (not_le.2 (ha v'' hv2).1)
    · exact absurd h (not_le.2 (ha v'' hv2).2)
  · rcases heq with h0 | heq
    · subst h0
      rcases hor with h | h
      · exact absurd h (not_le.2 (ha v'' hv2).1)
      · exact absurd h (not_le.2 (ha v'' hv2).2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv2
    have hb : b ∈ ({a, b} : Finset V) := by simp
    have ha' : a ∈ ({a, b} : Finset V) := by simp
    rcases hv2 with rfl | rfl
    · have e1 : (fun w => X w - CharVec u'' w + CharVec v'' w) = ym Z u b := by
        funext w; rw [hZdef]; simp only [ym]; ring
      have e2 : (fun w => Z w + CharVec u'' w - CharVec v'' w) = xm X u b := by
        funext w; rw [hZdef]; simp only [xm]; ring
      rw [e1, e2] at hor
      rcases hor with h | h
      · exact absurd (heq ▸ h) (not_le.2 (ha b hb).2)
      · exact absurd (heq ▸ h) (not_le.2 (ha b hb).1)
    · have e1 : (fun w => X w - CharVec u'' w + CharVec v'' w) = ym Z u a := by
        funext w; rw [hZdef]; simp only [ym]; ring
      have e2 : (fun w => Z w + CharVec u'' w - CharVec v'' w) = xm X u a := by
        funext w; rw [hZdef]; simp only [xm]; ring
      rw [e1, e2] at hor
      rcases hor with h | h
      · exact absurd (heq ▸ h) (not_le.2 (ha a ha').2)
      · exact absurd (heq ▸ h) (not_le.2 (ha a ha').1)

lemma loc (g : (V → ℤ) → WithTop ℝ) (H : ∀ q, QMw (PerturbedM g q))
    (X Z : V → ℤ) (hX : g X ≠ ⊤) (hZ : g Z ≠ ⊤)
    (u u' a b : V) (hua : u ≠ a) (hub : u ≠ b) (hu'a : u' ≠ a) (hu'b : u' ≠ b)
    (hZdef : Z = fun w => X w - CharVec u w - CharVec u' w + CharVec a w + CharVec b w) :
    Exch g X Z u a ∨ Exch g X Z u b := by
  by_contra hcon
  push Not at hcon
  have hfail : ∀ w ∈ ({a, b} : Finset V), g X + g Z < g (xm X u w) + g (ym Z u w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact lt_of_not_ge hcon.1
    · exact lt_of_not_ge hcon.2
  obtain ⟨s, hs⟩ := sepP g X Z hX hZ u {a, b} hfail
  obtain ⟨rX, hrX⟩ := WithTop.ne_top_iff_exists.1 hX
  obtain ⟨rZ, hrZ⟩ := WithTop.ne_top_iff_exists.1 hZ
  by_cases huu : u' = u
  · let p : V → ℝ := fun w => if w = u then 0 else -s w
    have hp : ∀ w ∈ ({a, b} : Finset V), p u - p w = s w := by
      intro w hw
      have : w ≠ u := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> exact fun h => by subst h; simp_all
      simp [p, this]
    exact loc_core g X Z hX hZ u u' a b hua hub hu'a hu'b hZdef p (H p) (hs p hp) (Or.inl huu)
  · let c : ℝ := (rX - rZ) - s a - s b
    let p : V → ℝ := fun w => if w = u then 0 else if w = u' then c else -s w
    have hp : ∀ w ∈ ({a, b} : Finset V), p u - p w = s w := by
      intro w hw
      have h1 : w ≠ u := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> exact fun h => by subst h; simp_all
      have h2 : w ≠ u' := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> exact fun h => by subst h; simp_all
      simp [p, h1, h2]
    have hpa : p a = -s a := by simp [p, Ne.symm hua, Ne.symm hu'a]
    have hpb : p b = -s b := by simp [p, Ne.symm hub, Ne.symm hu'b]
    have hpu : p u = 0 := by simp [p]
    have hpu' : p u' = c := by simp [p, huu]
    have heq : PerturbedM g p X = PerturbedM g p Z := by
      rw [pert_eq, pert_eq, hZdef, L_Z, ← hrX, show (fun w => X w - CharVec u w - CharVec u' w +
        CharVec a w + CharVec b w) = Z from hZdef.symm, ← hrZ, ← WithTop.coe_add,
        ← WithTop.coe_add, hpa, hpb, hpu, hpu']
      congr 1
      simp only [c]; ring
    exact loc_core g X Z hX hZ u u' a b hua hub hu'a hu'b hZdef p (H p) (hs p hp) (Or.inr heq)

end MQAux


namespace MQAux

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem main (n : ℕ) : ∀ (f : (V → ℤ) → WithTop ℝ), (∀ p, QMw (PerturbedM f p)) →
    ∀ x y : V → ℤ, f x ≠ ⊤ → f y ≠ ⊤ → N x y = n →
    ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y, Exch f x y u v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f H x y hx hy hn u hu
  by_contra hcon
  push Not at hcon
  have hfail : ∀ w ∈ SuppNeg x y, f x + f y < f (xm x u w) + f (ym y u w) :=
    fun w hw => lt_of_not_ge (hcon w hw)
  obtain ⟨s, hs⟩ := sepP f x y hx hy u (SuppNeg x y) hfail
  have huU := mem_pos.1 hu
  let p : V → ℝ := fun w => if w = u then 0 else -s w
  have hp : ∀ w ∈ SuppNeg x y, p u - p w = s w := by
    intro w hw
    have : w ≠ u := by rintro rfl; have := mem_neg.1 hw; omega
    simp [p, this]
  have ha := hs p hp
  set g := PerturbedM f p with hg
  have Hg : ∀ q, QMw (PerturbedM g q) := by
    intro q; rw [hg, pert_comp]; exact H _
  have hgx : g x ≠ ⊤ := (pert_ne_top f p x).2 hx
  have hgy : g y ≠ ⊤ := (pert_ne_top f p y).2 hy
  have hcon' : ∀ v ∈ SuppNeg x y, ¬ Exch g x y u v := by
    intro v hv; rw [hg, exch_pert]; exact hcon v hv
  have hxy : x ≠ y := by rintro rfl; omega
  obtain ⟨u1, hu1, v1, hv1, hor⟩ := H p x hgx y hgy hxy
  have hu1u : u1 ≠ u := by
    rintro rfl
    rcases hor with h | h
    · exact absurd h (not_le.2 (ha v1 hv1).1)
    · exact absurd h (not_le.2 (ha v1 hv1).2)
  have hne : (((SuppPos x y).erase u) ×ˢ (SuppNeg x y)).Nonempty :=
    ⟨(u1, v1), Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨hu1u, hu1⟩, hv1⟩⟩
  have hmem1 : (u1, v1) ∈ ((SuppPos x y).erase u) ×ˢ (SuppNeg x y) :=
    Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨hu1u, hu1⟩, hv1⟩
  have hdisj : ∀ a ∈ SuppPos x y, ∀ b ∈ SuppNeg x y, a ≠ b := by
    intro a ha b hb hab; subst hab; have := mem_pos.1 ha; have := mem_neg.1 hb; omega
  rcases hor with hxmove | hymove
  · -- x-move case
    obtain ⟨⟨u', v'⟩, hm, hmin⟩ := Finset.exists_min_image _
      (fun q : V × V => g (xm x q.1 q.2)) hne
    obtain ⟨hu'm, hv'⟩ := Finset.mem_product.1 hm
    obtain ⟨hu'u, hu'⟩ := Finset.mem_erase.1 hu'm
    simp only at hu'u hu' hv' hmin
    have hx' : g (xm x u' v') ≤ g x := le_trans (hmin (u1, v1) hmem1) hxmove
    have hu'v : y u' < x u' := mem_pos.1 hu'
    have hv'v : x v' < y v' := mem_neg.1 hv'
    have hlt : N (xm x u' v') y < n := hn ▸ N_xm_lt x y u' v' hu'v hv'v
    have hgx' : g (xm x u' v') ≠ ⊤ := ne_top_of_le_ne_top hgx hx'
    have huW : u ∈ SuppPos (xm x u' v') y := by
      rw [mem_pos]; simp only [xm, CharVec]
      rw [if_neg (Ne.symm hu'u), if_neg (hdisj u hu v' hv')]; omega
    obtain ⟨v, hv, hex⟩ := ih _ hlt g Hg (xm x u' v') y hgx' hgy rfl u huW
    have hvW : v ∈ SuppNeg x y := by
      have := mem_neg.1 hv; rw [mem_neg]; simp only [xm, CharVec] at this
      split_ifs at this with h1 h2 <;> subst_vars <;> omega
    have hz : g (xm (xm x u' v') u v) < g (xm x u' v') := by
      by_contra h
      push Not at h
      have := WithTop.add_lt_add_of_lt_of_le hgx' (ha v hvW).2 h
      unfold Exch at hex
      rw [add_comm (g y)] at this
      exact absurd hex (not_le.2 (by rwa [add_comm (g (xm _ u v))]))
    have hgz : g (xm (xm x u' v') u v) ≠ ⊤ := ne_top_of_lt hz
    have hloc := loc g Hg x (xm (xm x u' v') u v) hgx hgz u u' v v'
      (hdisj u hu v hvW) (hdisj u hu v' hv') (hdisj u' hu' v hvW) (hdisj u' hu' v' hv')
      (by funext w; simp only [xm]; ring)
    rcases hloc with h | h
    · unfold Exch at h
      rw [show ym (xm (xm x u' v') u v) u v = xm x u' v' by funext w; simp only [xm, ym]; ring] at h
      have := WithTop.add_lt_add_of_lt_of_le hgz (ha v hvW).1 hz.le
      exact absurd h (not_le.2 this)
    · unfold Exch at h
      rw [show ym (xm (xm x u' v') u v) u v' = xm x u' v by funext w; simp only [xm, ym]; ring] at h
      have hm2 : (u', v) ∈ ((SuppPos x y).erase u) ×ˢ (SuppNeg x y) :=
        Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨hu'u, hu'⟩, hvW⟩
      have := WithTop.add_lt_add_of_lt_of_le hgz (ha v' hv').1 (hz.le.trans (hmin _ hm2))
      exact absurd h (not_le.2 this)
  · -- y-move case
    obtain ⟨⟨u', v'⟩, hm, hmin⟩ := Finset.exists_min_image _
      (fun q : V × V => g (ym y q.1 q.2)) hne
    obtain ⟨hu'm, hv'⟩ := Finset.mem_product.1 hm
    obtain ⟨hu'u, hu'⟩ := Finset.mem_erase.1 hu'm
    simp only at hu'u hu' hv' hmin
    have hy' : g (ym y u' v') ≤ g y := le_trans (hmin (u1, v1) hmem1) hymove
    have hu'v : y u' < x u' := mem_pos.1 hu'
    have hv'v : x v' < y v' := mem_neg.1 hv'
    have hlt : N x (ym y u' v') < n := hn ▸ N_ym_lt x y u' v' hu'v hv'v
    have hgy' : g (ym y u' v') ≠ ⊤ := ne_top_of_le_ne_top hgy hy'
    have huW : u ∈ SuppPos x (ym y u' v') := by
      rw [mem_pos]; simp only [ym, CharVec]
      rw [if_neg (Ne.symm hu'u), if_neg (hdisj u hu v' hv')]; omega
    obtain ⟨v, hv, hex⟩ := ih _ hlt g Hg x (ym y u' v') hgx hgy' rfl u huW
    have hvW : v ∈ SuppNeg x y := by
      have := mem_neg.1 hv; rw [mem_neg]; simp only [ym, CharVec] at this
      split_ifs at this with h1 h2 <;> subst_vars <;> omega
    have hz : g (ym (ym y u' v') u v) < g (ym y u' v') := by
      by_contra h
      push Not at h
      have := WithTop.add_lt_add_of_lt_of_le hgy' (ha v hvW).1 h
      unfold Exch at hex
      exact absurd hex (not_le.2 this)
    have hgz : g (ym (ym y u' v') u v) ≠ ⊤ := ne_top_of_lt hz
    have hloc := loc g Hg (ym (ym y u' v') u v) y hgz hgy u u' v v'
      (hdisj u hu v hvW) (hdisj u hu v' hv') (hdisj u' hu' v hvW) (hdisj u' hu' v' hv')
      (by funext w; simp only [ym]; ring)
    rcases hloc with h | h
    · unfold Exch at h
      rw [show xm (ym (ym y u' v') u v) u v = ym y u' v' by funext w; simp only [xm, ym]; ring] at h
      have := WithTop.add_lt_add_of_lt_of_le hgy hz (ha v hvW).2.le
      exact absurd h (not_le.2 this)
    · unfold Exch at h
      rw [show xm (ym (ym y u' v') u v) u v' = ym y u' v by funext w; simp only [xm, ym]; ring] at h
      have hm2 : (u', v) ∈ ((SuppPos x y).erase u) ×ˢ (SuppNeg x y) :=
        Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨hu'u, hu'⟩, hvW⟩
      have := WithTop.add_lt_add_of_lt_of_le hgy (hz.trans_le (hmin _ hm2)) (ha v' hv').2.le
      exact absurd h (not_le.2 this)

end MQAux

open MQAux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    MExchangeAxiom f ↔ ∀ p : V → ℝ, QMw (PerturbedM f p) := by
  constructor
  · intro hM p x hx y hy hxy
    have hx' : f x ≠ ⊤ := (pert_ne_top f p x).1 hx
    have hy' : f y ≠ ⊤ := (pert_ne_top f p y).1 hy
    have hpos : (SuppPos x y).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      obtain ⟨w, hw⟩ := Function.ne_iff.1 hxy
      have hw' : x w < y w := by
        rcases lt_or_gt_of_ne hw with h | h
        · exact h
        · have : w ∈ SuppPos x y := mem_pos.2 h
          rw [hne] at this; simp at this
      obtain ⟨v, hv, -⟩ := hM y hy' x hx' w (mem_pos.2 hw')
      have : v ∈ SuppPos x y := mem_pos.2 (mem_neg.1 hv)
      rw [hne] at this; simp at this
    obtain ⟨u, hu⟩ := hpos
    obtain ⟨v, hv, hex⟩ := hM x hx' y hy' u hu
    have hex' : Exch (PerturbedM f p) x y u v := (exch_pert f p x y u v).2 hex
    refine ⟨u, hu, v, hv, ?_⟩
    by_contra hh
    push Not at hh
    have := WithTop.add_lt_add_of_lt_of_le hy hh.1 hh.2.le
    exact absurd hex' (not_le.2 this)
  · intro H x hx y hy u hu
    exact main _ f H x y hx hy rfl u hu
