-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsB.negative_cycle_criterion_msfp2_integer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:30:56.528758+00:00
-- url     : https://prove2.me/submissions/7baa82b6-1cec-4424-b342-f63c7d36a824

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2Z

open Classical
open scoped Pointwise
open DiscreteConvex.NetworkFlowsB

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace P25a32c21

namespace MIAux

variable {W : Type*} [Fintype W] [DecidableEq W]

def CharVec (u w : W) : ℤ := if w = u then 1 else 0
def xm (x : W → ℤ) (u v : W) : W → ℤ := fun w => x w - CharVec u w + CharVec v w
def ym (y : W → ℤ) (u v : W) : W → ℤ := fun w => y w + CharVec u w - CharVec v w
def L (p : W → ℝ) (x : W → ℤ) : ℝ := ∑ w, p w * (x w : ℝ)
def pf (g : (W → ℤ) → WithTop ℝ) (p : W → ℝ) (x : W → ℤ) : WithTop ℝ := g x + ((L p x : ℝ) : WithTop ℝ)

lemma exch {g : (W → ℤ) → WithTop ℝ} (hg : MExchangeAxiom g) {x y : W → ℤ}
    (hx : g x ≠ ⊤) (hy : g y ≠ ⊤) {u : W} (hu : y u < x u) :
    ∃ v, x v < y v ∧ g (xm x u v) + g (ym y u v) ≤ g x + g y := by
  obtain ⟨v, hv, h⟩ := hg x hx y hy u (by simp [SuppPos, hu])
  exact ⟨v, by simpa [SuppNeg] using hv, h⟩

lemma sum_char (p : W → ℝ) (u : W) : ∑ w, p w * ((CharVec u w : ℤ) : ℝ) = p u := by
  simp [CharVec]

lemma L_xm (p : W → ℝ) (x : W → ℤ) (u v : W) : L p (xm x u v) = L p x - p u + p v := by
  simp only [L, xm]; push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_char]

lemma L_ym (p : W → ℝ) (x : W → ℤ) (u v : W) : L p (ym x u v) = L p x + p u - p v := by
  simp only [L, ym]; push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_char]

lemma pf_ne_top (g : (W → ℤ) → WithTop ℝ) (p : W → ℝ) (x : W → ℤ) :
    pf g p x ≠ ⊤ ↔ g x ≠ ⊤ := by
  rw [pf, WithTop.add_ne_top]; simp

lemma pf_exch (g : (W → ℤ) → WithTop ℝ) (hg : MExchangeAxiom g) (p : W → ℝ) :
    MExchangeAxiom (pf g p) := by
  intro x hx y hy u hu
  have hx' : g x ≠ ⊤ := (pf_ne_top g p x).1 hx
  have hy' : g y ≠ ⊤ := (pf_ne_top g p y).1 hy
  obtain ⟨v, hv, h⟩ := hg x hx' y hy' u hu
  refine ⟨v, hv, ?_⟩
  change pf g p (xm x u v) + pf g p (ym y u v) ≤ pf g p x + pf g p y
  change g (xm x u v) + g (ym y u v) ≤ g x + g y at h
  simp only [pf, L_xm, L_ym]
  have e1 : g (xm x u v) + ((L p x - p u + p v : ℝ) : WithTop ℝ) +
      (g (ym y u v) + ((L p y + p u - p v : ℝ) : WithTop ℝ))
      = (g (xm x u v) + g (ym y u v)) + (((L p x + L p y) : ℝ) : WithTop ℝ) := by
    rw [show (L p x + L p y) = (L p x - p u + p v) + (L p y + p u - p v) by ring,
      WithTop.coe_add]
    ac_rfl
  have e2 : g x + ((L p x : ℝ) : WithTop ℝ) + (g y + ((L p y : ℝ) : WithTop ℝ))
      = (g x + g y) + (((L p x + L p y) : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_add]; ac_rfl
  rw [e1, e2]
  exact add_le_add_left h _

def bulk (u v : ℕ → W) (x : W → ℤ) (s : Finset ℕ) : W → ℤ :=
  fun w => x w - ∑ i ∈ s, (CharVec (u i) w - CharVec (v i) w)

lemma two_lt {X Y Z T : WithTop ℝ} {t : ℝ}
    (h : Z + T ≤ X + Y) (hX : X = t) (hY : Y = t) (hZ : (t : WithTop ℝ) < Z)
    (hT : (t : WithTop ℝ) < T) : False := by
  subst hX hY
  induction Z using WithTop.recTopCoe with
  | top => simp at h
  | coe Z =>
    induction T using WithTop.recTopCoe with
    | top => simp at h
    | coe T =>
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
      rw [WithTop.coe_lt_coe] at hZ hT; linarith

lemma le_sub_of {Z : WithTop ℝ} {a s : ℝ} (h : Z + (a : WithTop ℝ) ≤ (s : WithTop ℝ)) :
    Z ≤ ((s - a : ℝ) : WithTop ℝ) := by
  induction Z using WithTop.recTopCoe with
  | top => simp at h
  | coe Z => rw [← WithTop.coe_add, WithTop.coe_le_coe] at h; rw [WithTop.coe_le_coe]; linarith

lemma coe_add2 (a b : ℝ) : (a : WithTop ℝ) + (b : WithTop ℝ) = ((a + b : ℝ) : WithTop ℝ) :=
  (WithTop.coe_add a b).symm

lemma diag_up {g : (W → ℤ) → WithTop ℝ} (hg : MExchangeAxiom g) (x : W → ℤ) (α κ : ℝ)
    (hx : g x = α) (a b c d : W) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : g (xm x a b) = ((α + κ : ℝ) : WithTop ℝ)) (h2 : g (xm x c d) = ((α + κ : ℝ) : WithTop ℝ))
    (h3 : ((α + κ : ℝ) : WithTop ℝ) < g (xm x a d)) (h4 : ((α + κ : ℝ) : WithTop ℝ) < g (xm x c b)) :
    g (xm (xm x c d) a b) ≤ ((α + 2 * κ : ℝ) : WithTop ℝ) := by
  obtain ⟨v, hv, h⟩ := exch hg (x := xm x a b) (y := xm x c d) (by rw [h1]; simp) (by rw [h2]; simp)
    (u := b) (by simp [xm, CharVec, hab.symm, hbc, hbd])
  have hv' : v = a ∨ v = d := by
    by_contra hh; push Not at hh
    simp only [xm, CharVec] at hv
    split_ifs at hv <;> simp_all <;> omega
  rcases hv' with rfl | rfl
  · have e1 : xm (xm x v b) b v = x := by
      funext w; simp only [xm, CharVec]; split_ifs <;> omega
    have e2 : ym (xm x c d) b v = xm (xm x c d) v b := by
      funext w; simp only [xm, ym, CharVec]; split_ifs <;> omega
    rw [e1, e2, h1, h2, hx, coe_add2, add_comm] at h
    have := le_sub_of h
    convert this using 2; ring
  · have e1 : xm (xm x a b) b v = xm x a v := by
      funext w; simp only [xm, CharVec]; split_ifs <;> omega
    have e2 : ym (xm x c v) b v = xm x c b := by
      funext w; simp only [xm, ym, CharVec]; split_ifs <;> omega
    rw [e1, e2] at h
    exact (two_lt h h1 h2 h3 h4).elim

lemma low {g : (W → ℤ) → WithTop ℝ} (hg : MExchangeAxiom g) (x : W → ℤ) (α κ : ℝ)
    (hx : g x = α) (a b c d : W) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (hab : a ≠ b)
    (h2 : g (xm x c d) = ((α + κ : ℝ) : WithTop ℝ))
    (h3 : ((α + κ : ℝ) : WithTop ℝ) < g (xm x a d)) (h4 : ((α + κ : ℝ) : WithTop ℝ) < g (xm x c b)) :
    (((α + κ : ℝ) : WithTop ℝ) ≤ g (xm x a b) → ((α + 2 * κ : ℝ) : WithTop ℝ) ≤ g (xm (xm x c d) a b)) ∧
    (((α + κ : ℝ) : WithTop ℝ) < g (xm x a b) → ((α + 2 * κ : ℝ) : WithTop ℝ) < g (xm (xm x c d) a b)) := by
  by_cases hZ : g (xm (xm x c d) a b) = ⊤
  · rw [hZ]; exact ⟨fun _ => le_top, fun _ => WithTop.coe_lt_top _⟩
  obtain ⟨v, hv, h⟩ := exch hg (x := xm (xm x c d) a b) (y := x) hZ (by rw [hx]; simp)
    (u := d) (by simp [xm, CharVec, hcd.symm, had.symm, hbd.symm])
  have hv' : v = c ∨ v = a := by
    by_contra hh; push Not at hh
    simp only [xm, CharVec] at hv
    split_ifs at hv <;> simp_all <;> omega
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hZ
  rcases hv' with rfl | rfl
  · have e1 : xm (xm (xm x v d) a b) d v = xm x a b := by
      funext w; simp only [xm, CharVec]; split_ifs <;> omega
    have e2 : ym x d v = xm x v d := by
      funext w; simp only [xm, ym, CharVec]; split_ifs <;> omega
    rw [e1, e2, h2, hx, ← hz] at h
    rw [← hz]
    induction hA : g (xm x a b) using WithTop.recTopCoe with
    | top => rw [hA] at h; simp at h
    | coe A =>
      rw [hA] at h
      rw [coe_add2, coe_add2, WithTop.coe_le_coe] at h
      constructor
      · intro hl; rw [WithTop.coe_le_coe] at hl ⊢; linarith
      · intro hl; rw [WithTop.coe_lt_coe] at hl ⊢; linarith
  · have e1 : xm (xm (xm x c d) v b) d v = xm x c b := by
      funext w; simp only [xm, CharVec]; split_ifs <;> omega
    have e2 : ym x d v = xm x v d := by
      funext w; simp only [xm, ym, CharVec]; split_ifs <;> omega
    rw [e1, e2, hx, ← hz] at h
    rw [← hz]
    have key : ((α + 2 * κ : ℝ) : WithTop ℝ) < (z : WithTop ℝ) := by
      induction hA : g (xm x c b) using WithTop.recTopCoe with
      | top => rw [hA] at h; simp at h
      | coe A =>
        induction hB : g (xm x v d) using WithTop.recTopCoe with
        | top => rw [hB] at h; simp at h
        | coe B =>
          rw [hA, hB] at h; rw [hA] at h4; rw [hB] at h3
          rw [coe_add2, coe_add2, WithTop.coe_le_coe] at h
          rw [WithTop.coe_lt_coe] at h3 h4 ⊢; linarith
    exact ⟨fun _ => key.le, fun _ => key⟩

lemma ML {g : (W → ℤ) → WithTop ℝ} (hg : MExchangeAxiom g) (u v : ℕ → W) (κ : ℝ)
    (s : Finset ℕ) : ∀ (x : W → ℤ) (α : ℝ), g x = α →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → u i ≠ u j) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i ≠ v j) →
    (∀ i ∈ s, ∀ j ∈ s, u i ≠ v j) →
    (∀ i ∈ s, g (xm x (u i) (v i)) = ((α + κ : ℝ) : WithTop ℝ)) →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ((α + κ : ℝ) : WithTop ℝ) < g (xm x (u i) (v j))) →
    g (bulk u v x s) ≤ ((α + s.card * κ : ℝ) : WithTop ℝ) := by
  induction s using Finset.induction_on with
  | empty =>
    intro x α hx _ _ _ _ _
    have : bulk u v x ∅ = x := by funext w; simp [bulk]
    rw [this, hx]; simp
  | insert m s0 hm IH =>
    intro x α hx hu hv huv hd ho
    have mem : m ∈ insert m s0 := Finset.mem_insert_self _ _
    have sub : ∀ i ∈ s0, i ∈ insert m s0 := fun i hi => Finset.mem_insert_of_mem hi
    have nm : ∀ i ∈ s0, i ≠ m := fun i hi h => hm (h ▸ hi)
    have key := IH (xm x (u m) (v m)) (α + κ) (hd m mem)
      (fun i hi j hj hij => hu i (sub i hi) j (sub j hj) hij)
      (fun i hi j hj hij => hv i (sub i hi) j (sub j hj) hij)
      (fun i hi j hj => huv i (sub i hi) j (sub j hj))
      (by
        intro i hi
        have hi' := sub i hi
        apply le_antisymm
        · have := diag_up hg x α κ hx (u i) (v i) (u m) (v m) (huv i hi' i hi')
            (hu i hi' m mem (nm i hi)) (huv i hi' m mem) (fun h => huv m mem i hi' h.symm)
            (hv i hi' m mem (nm i hi)) (huv m mem m mem) (hd i hi') (hd m mem)
            (ho i hi' m mem (nm i hi)) (ho m mem i hi' (nm i hi).symm)
          convert this using 2; ring
        · have := (low hg x α κ hx (u i) (v i) (u m) (v m) (hu i hi' m mem (nm i hi))
            (huv i hi' m mem) (fun h => huv m mem i hi' h.symm) (hv i hi' m mem (nm i hi))
            (huv m mem m mem) (huv i hi' i hi') (hd m mem)
            (ho i hi' m mem (nm i hi)) (ho m mem i hi' (nm i hi).symm)).1 (hd i hi').ge
          convert this using 2; ring)
      (by
        intro i hi j hj hij
        have hi' := sub i hi
        have hj' := sub j hj
        have := (low hg x α κ hx (u i) (v j) (u m) (v m) (hu i hi' m mem (nm i hi))
            (huv i hi' m mem) (fun h => huv m mem j hj' h.symm) (hv j hj' m mem (nm j hj))
            (huv m mem m mem) (huv i hi' j hj') (hd m mem)
            (ho i hi' m mem (nm i hi)) (ho m mem j hj' (nm j hj).symm)).2 (ho i hi' j hj' hij)
        convert this using 2; ring)
    have e : bulk u v x (insert m s0) = bulk u v (xm x (u m) (v m)) s0 := by
      funext w; simp only [bulk, xm, Finset.sum_insert hm]; ring
    rw [e]
    convert key using 2
    rw [Finset.card_insert_of_notMem hm]; push_cast; ring

def N (x y : W → ℤ) : ℕ := ∑ w, (x w - y w).natAbs

lemma N_ym_lt (x y : W → ℤ) (u v : W) (hu : y u < x u) (hv : x v < y v) :
    N x (ym y u v) < N x y := by
  unfold N ym
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    split_ifs with h1 h2 <;> subst_vars <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [CharVec]
    split_ifs with h1 h2 <;> subst_vars <;> omega

lemma LG {g : (W → ℤ) → WithTop ℝ} (hg : MExchangeAxiom g) (x : W → ℤ) (hx : g x ≠ ⊤)
    (hloc : ∀ a b, g x ≤ g (xm x a b)) : ∀ z, g x ≤ g z := by
  intro z
  induction hn : N x z using Nat.strong_induction_on generalizing z with
  | _ n IH =>
    by_cases hz : g z = ⊤
    · rw [hz]; exact le_top
    by_cases hex : ∃ u, z u < x u
    · obtain ⟨u, hu⟩ := hex
      obtain ⟨v, hv, h⟩ := exch hg hx hz hu
      have h1 := hloc u v
      have h2 : g (ym z u v) ≤ g z := by
        obtain ⟨X, hX⟩ := WithTop.ne_top_iff_exists.1 hx
        rw [← hX] at h h1
        induction hA : g (xm x u v) using WithTop.recTopCoe with
        | top => rw [hA] at h; simp at h; exact absurd h hz
        | coe A =>
          rw [hA] at h h1
          rw [WithTop.coe_le_coe] at h1
          induction hB : g (ym z u v) using WithTop.recTopCoe with
          | top => rw [hB] at h; simp at h; exact absurd h hz
          | coe B =>
            rw [hB] at h
            induction hC : g z using WithTop.recTopCoe with
            | top => exact le_top
            | coe C =>
              rw [hC] at h
              rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
              rw [WithTop.coe_le_coe]; linarith
      exact (IH _ (hn ▸ N_ym_lt x z u v hu hv) (ym z u v) rfl).trans h2
    · push Not at hex
      by_cases hzx : z = x
      · rw [hzx]
      have : ∃ u, x u < z u := by
        by_contra hh; push Not at hh
        exact hzx (funext fun w => le_antisymm (hh w) (hex w))
      obtain ⟨u, hu⟩ := this
      obtain ⟨v, hv, _⟩ := exch hg hz hx hu
      exact absurd (hex v) (not_le.2 hv)

lemma tri {g : (W → ℤ) → WithTop ℝ} (hg : MExchangeAxiom g) (x : W → ℤ) (α : ℝ) (hx : g x = α)
    (a b c : W) (hab : a ≠ b) (hbc : b ≠ c) :
    g (xm x a c) + (α : WithTop ℝ) ≤ g (xm x a b) + g (xm x b c) := by
  by_cases h1 : g (xm x a b) = ⊤
  · rw [h1]; simp
  by_cases h2 : g (xm x b c) = ⊤
  · rw [h2]; simp
  obtain ⟨v, hv, h⟩ := exch hg h1 h2 (u := b) (by simp [xm, CharVec, hab.symm, hbc])
  have hv' : v = a ∨ v = c := by
    by_contra hh; push Not at hh
    simp only [xm, CharVec] at hv
    split_ifs at hv <;> simp_all <;> omega
  rcases hv' with rfl | rfl
  · have e1 : xm (xm x v b) b v = x := by
      funext w; simp only [xm, CharVec]; split_ifs <;> omega
    have e2 : ym (xm x b c) b v = xm x v c := by
      funext w; simp only [xm, ym, CharVec]; split_ifs <;> omega
    rw [e1, e2, hx, add_comm] at h; exact h
  · have e1 : xm (xm x a b) b v = xm x a v := by
      funext w; simp only [xm, CharVec]; split_ifs <;> omega
    have e2 : ym (xm x b v) b v = x := by
      funext w; simp only [xm, ym, CharVec]; split_ifs <;> omega
    rw [e1, e2, hx] at h; exact h

lemma xm_self (x : W → ℤ) (a : W) : xm x a a = x := by
  funext w; simp [xm]

lemma mod_succ (k n : ℕ) (hn : 0 < n) : (k + 1) % n = if k % n + 1 = n then 0 else k % n + 1 := by
  rw [Nat.add_mod]
  have hk := Nat.mod_lt k hn
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  · have : n = 1 := by omega
    subst this; simp [Nat.mod_one]

lemma per_mul {α : Type*} (γ : ℕ → α) (n : ℕ) (hp : ∀ k, γ (k + n) = γ k) (k q : ℕ) :
    γ (k + n * q) = γ k := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]

lemma shift_sum {M : Type*} [AddCommGroup M] (G : ℕ → M) (n : ℕ) (hG : G n = G 0) :
    ∑ i ∈ Finset.range n, G (i + 1) = ∑ i ∈ Finset.range n, G i := by
  have h1 := Finset.sum_range_succ' G n
  have h2 := Finset.sum_range_succ G n
  rw [hG] at h2
  exact add_right_cancel (h1.symm.trans h2)

end MIAux

namespace MIGraph

variable {W L : Type*} [Fintype W] [DecidableEq W]
variable (E : W → W → L → Prop) (c : W → W → L → ℝ)

def IsWalk (δ : ℕ → W) (τ : ℕ → L) (m : ℕ) : Prop := ∀ k < m, E (δ k) (δ (k + 1)) (τ k)

def wt (δ : ℕ → W) (τ : ℕ → L) (m : ℕ) : ℝ := ∑ k ∈ Finset.range m, c (δ k) (δ (k + 1)) (τ k)

def cutF {α : Type*} (δ : ℕ → α) (a b : ℕ) : ℕ → α := fun k => if k < a then δ k else δ (k + (b - a))
def shF {α : Type*} (δ : ℕ → α) (a : ℕ) : ℕ → α := fun k => δ (a + k)

variable {E c}

lemma cut_walk {δ : ℕ → W} {τ : ℕ → L} {m a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) (he : δ a = δ b)
    (hw : IsWalk E δ τ m) : IsWalk E (cutF δ a b) (cutF τ a b) (m - (b - a)) := by
  intro k hk
  simp only [cutF]
  by_cases h1 : k < a
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : k + 1 < a
    · rw [if_pos h2]; exact hw k (by omega)
    · rw [if_neg h2, show k + 1 + (b - a) = b by omega, ← he, show a = k + 1 by omega]
      exact hw k (by omega)
  · rw [if_neg h1, if_neg h1, if_neg (by omega), show k + 1 + (b - a) = k + (b - a) + 1 by omega]
    exact hw _ (by omega)

lemma sh_walk {δ : ℕ → W} {τ : ℕ → L} {m a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m)
    (hw : IsWalk E δ τ m) : IsWalk E (shF δ a) (shF τ a) (b - a) := by
  intro k hk
  simp only [shF, show a + (k + 1) = a + k + 1 by omega]
  exact hw _ (by omega)

lemma wt_split (δ : ℕ → W) (τ : ℕ → L) {m a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) (he : δ a = δ b) :
    wt c δ τ m = wt c (cutF δ a b) (cutF τ a b) (m - (b - a)) + wt c (shF δ a) (shF τ a) (b - a) := by
  simp only [wt]
  rw [show m = a + (b - a) + (m - b) by omega, Finset.sum_range_add, Finset.sum_range_add,
    show a + (b - a) + (m - b) - (b - a) = a + (m - b) by omega, Finset.sum_range_add]
  have h1 : ∑ k ∈ Finset.range a, c (cutF δ a b k) (cutF δ a b (k + 1)) (cutF τ a b k) =
      ∑ k ∈ Finset.range a, c (δ k) (δ (k + 1)) (τ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [cutF, if_pos hk]
    by_cases h2 : k + 1 < a
    · rw [if_pos h2]
    · rw [if_neg h2, show k + 1 + (b - a) = b by omega, ← he, show a = k + 1 by omega]
  have h2 : ∑ k ∈ Finset.range (m - b), c (cutF δ a b (a + k)) (cutF δ a b (a + k + 1))
      (cutF τ a b (a + k)) = ∑ k ∈ Finset.range (m - b), c (δ (a + (b - a) + k))
      (δ (a + (b - a) + k + 1)) (τ (a + (b - a) + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [cutF, if_neg (show ¬ a + k < a by omega), if_neg (show ¬ a + k + 1 < a by omega),
      show a + k + (b - a) = a + (b - a) + k by omega,
      show a + k + 1 + (b - a) = a + (b - a) + k + 1 by omega]
  have h3 : ∑ k ∈ Finset.range (b - a), c (shF δ a k) (shF δ a (k + 1)) (shF τ a k) =
      ∑ k ∈ Finset.range (b - a), c (δ (a + k)) (δ (a + k + 1)) (τ (a + k)) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [shF, show a + (k + 1) = a + k + 1 by omega]
  rw [h1, h2, h3]; ring

lemma cut_end {α : Type*} (δ : ℕ → α) {m a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) :
    cutF δ a b (m - (b - a)) = δ m := by
  simp only [cutF, if_neg (show ¬ m - (b - a) < a by omega), show m - (b - a) + (b - a) = m by omega]

lemma cut_start {α : Type*} (δ : ℕ → α) {a b : ℕ} (he : δ a = δ b) :
    cutF δ a b 0 = δ 0 := by
  simp only [cutF]
  split_ifs with h
  · rfl
  · rw [show a = 0 by omega] at he ⊢; simp [← he]

lemma pigeon (δ : ℕ → W) (m : ℕ) (hm : Fintype.card W < m) :
    ∃ a b, a < b ∧ b < m ∧ δ a = δ b := by
  obtain ⟨i, hi, j, hj, hij, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range m) (t := (Finset.univ : Finset W)) (f := δ)
    (by simpa using hm) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.mem_range] at hi hj
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact ⟨i, j, h', hj, h⟩
  · exact ⟨j, i, h', hi, h.symm⟩

lemma closed_ge (μ : ℝ)
    (hshort : ∀ m δ τ, 0 < m → m ≤ Fintype.card W → IsWalk E δ τ m → δ m = δ 0 →
      (m : ℝ) * μ ≤ wt c δ τ m) :
    ∀ m δ τ, IsWalk E δ τ m → δ m = δ 0 → (m : ℝ) * μ ≤ wt c δ τ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro δ τ hw hc
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [wt]
    by_cases hN : m ≤ Fintype.card W
    · exact hshort m δ τ hpos hN hw hc
    push Not at hN
    obtain ⟨a, b, hab, hbm, he⟩ := pigeon δ m hN
    rw [wt_split δ τ hab.le hbm.le he]
    have h1 := IH (m - (b - a)) (by omega) _ _ (cut_walk hab.le hbm.le he hw)
      (by rw [cut_end δ hab.le hbm.le, cut_start δ he, hc])
    have h2 := IH (b - a) (by omega) _ _ (sh_walk hab.le hbm.le hw)
      (by simp only [shF, Nat.add_zero, show a + (b - a) = b by omega, he])
    have : ((m - (b - a) : ℕ) : ℝ) + ((b - a : ℕ) : ℝ) = m := by
      rw [← Nat.cast_add, show m - (b - a) + (b - a) = m by omega]
    have e : (m : ℝ) * μ = ((m - (b - a) : ℕ) : ℝ) * μ + ((b - a : ℕ) : ℝ) * μ := by
      rw [← this]; ring
    linarith

lemma walk_ge (hnn : ∀ m δ τ, IsWalk E δ τ m → δ m = δ 0 → 0 ≤ wt c δ τ m) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ a b l, -M ≤ c a b l) :
    ∀ m δ τ, IsWalk E δ τ m → -(Fintype.card W * M) ≤ wt c δ τ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro δ τ hw
    by_cases hN : m ≤ Fintype.card W
    · have : -(m * M) ≤ wt c δ τ m := by
        simp only [wt]
        have := Finset.sum_le_sum (s := Finset.range m) (fun k _ => hM (δ k) (δ (k + 1)) (τ k))
        simpa using this
      have h2 : (m : ℝ) * M ≤ Fintype.card W * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hM0
      linarith
    push Not at hN
    obtain ⟨a, b, hab, hbm, he⟩ := pigeon δ m hN
    rw [wt_split δ τ hab.le hbm.le he]
    have h1 := IH (m - (b - a)) (by omega) _ _ (cut_walk hab.le hbm.le he hw)
    have h2 := hnn (b - a) _ _ (sh_walk hab.le hbm.le hw)
      (by simp only [shF, Nat.add_zero, show a + (b - a) = b by omega, he])
    linarith

lemma potential [Fintype L] [Nonempty L]
    (hnn : ∀ m δ τ, IsWalk E δ τ m → δ m = δ 0 → 0 ≤ wt c δ τ m) :
    ∃ π : W → ℝ, ∀ a b l, E a b l → π b ≤ π a + c a b l := by
  classical
  set M : ℝ := ∑ a, ∑ b, ∑ l, |c a b l| with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hM : ∀ a b l, -M ≤ c a b l := by
    intro a b l
    have h1 : |c a b l| ≤ M := by
      calc |c a b l| ≤ ∑ l, |c a b l| :=
            Finset.single_le_sum (f := fun l => |c a b l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
        _ ≤ ∑ b, ∑ l, |c a b l| :=
            Finset.single_le_sum (f := fun b => ∑ l, |c a b l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ b)
        _ ≤ M :=
            Finset.single_le_sum (f := fun a => ∑ b, ∑ l, |c a b l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ a)
    linarith [neg_abs_le (c a b l)]
  let S : W → Set ℝ := fun b => {r | ∃ δ τ m, IsWalk E δ τ m ∧ δ m = b ∧ wt c δ τ m = r}
  have hne : ∀ b, (S b).Nonempty := fun b =>
    ⟨0, fun _ => b, fun _ => Classical.arbitrary L, 0, fun k hk => absurd hk (Nat.not_lt_zero _),
      rfl, by simp [wt]⟩
  have hbdd : ∀ b, BddBelow (S b) := fun b => ⟨-(Fintype.card W * M), by
    rintro r ⟨δ, τ, m, hw, _, rfl⟩; exact walk_ge hnn M hM0 hM m δ τ hw⟩
  refine ⟨fun b => sInf (S b), fun a b l hE => ?_⟩
  have : sInf (S b) - c a b l ≤ sInf (S a) := by
    apply le_csInf (hne a)
    rintro r ⟨δ, τ, m, hw, hend, rfl⟩
    have hmem : wt c δ τ m + c a b l ∈ S b := by
      refine ⟨fun k => if k ≤ m then δ k else b, fun k => if k < m then τ k else l, m + 1, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hkm : k < m
        · simp only [if_pos hkm.le, if_pos hkm, if_pos (show k + 1 ≤ m by omega)]
          exact hw k hkm
        · have : k = m := by omega
          subst this
          simp only [le_refl, if_true, lt_irrefl, if_false, show ¬ k + 1 ≤ k by omega, hend]
          exact hE
      · simp
      · simp only [wt, Finset.sum_range_succ, le_refl, if_true, lt_irrefl, if_false,
          show ¬ m + 1 ≤ m by omega, hend]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        simp only [if_pos hk.le, if_pos hk, if_pos (show k + 1 ≤ m by omega)]
    have := csInf_le (hbdd b) hmem
    linarith
  linarith

lemma min_mean [Fintype L] [DecidableEq L]
    (hneg : ∃ m δ τ, IsWalk E δ τ m ∧ δ m = δ 0 ∧ wt c δ τ m < 0) :
    ∃ μ : ℝ, μ < 0 ∧ (∀ m δ τ, IsWalk E δ τ m → δ m = δ 0 → (m : ℝ) * μ ≤ wt c δ τ m) ∧
      ∃ m δ τ, 0 < m ∧ IsWalk E δ τ m ∧ δ m = δ 0 ∧ wt c δ τ m = m * μ := by
  classical
  set N := Fintype.card W
  have hshort : ∃ m δ τ, 0 < m ∧ m ≤ N ∧ IsWalk E δ τ m ∧ δ m = δ 0 ∧ wt c δ τ m < 0 := by
    by_contra hh
    push Not at hh
    obtain ⟨m, δ, τ, hw, hc, hlt⟩ := hneg
    have := closed_ge (E := E) (c := c) 0 (fun m δ τ hm hmN hw hc => by
      simpa using hh m δ τ hm hmN hw hc) m δ τ hw hc
    simp at this; linarith
  obtain ⟨m1, δ1, τ1, hm1, hm1N, hw1, hc1, hneg1⟩ := hshort
  let extW : (Fin (N + 1) → W) → ℕ → W := fun φ k => φ ⟨min k N, by omega⟩
  let extL : (Fin (N + 1) → L) → ℕ → L := fun φ k => φ ⟨min k N, by omega⟩
  let valid : Fin (N + 1) × (Fin (N + 1) → W) × (Fin (N + 1) → L) → Prop := fun C =>
    0 < (C.1 : ℕ) ∧ IsWalk E (extW C.2.1) (extL C.2.2) C.1 ∧ extW C.2.1 C.1 = extW C.2.1 0
  let S := Finset.univ.filter valid
  let mean : Fin (N + 1) × (Fin (N + 1) → W) × (Fin (N + 1) → L) → ℝ := fun C =>
    wt c (extW C.2.1) (extL C.2.2) C.1 / (C.1 : ℕ)
  have emb : ∀ (m : ℕ) (δ : ℕ → W) (τ : ℕ → L), m ≤ N → ∃ C : Fin (N + 1) × (Fin (N + 1) → W) × (Fin (N + 1) → L),
      (C.1 : ℕ) = m ∧ (∀ k ≤ N, extW C.2.1 k = δ k) ∧ (∀ k ≤ N, extL C.2.2 k = τ k) := by
    intro m δ τ hm
    refine ⟨(⟨m, by omega⟩, fun i => δ i, fun i => τ i), rfl, fun k hk => ?_, fun k hk => ?_⟩ <;>
      simp [extW, extL, Nat.min_eq_left hk]
  have transfer : ∀ (m : ℕ) (δ : ℕ → W) (τ : ℕ → L) (C : Fin (N + 1) × (Fin (N + 1) → W) × (Fin (N + 1) → L)),
      m ≤ N → (C.1 : ℕ) = m → (∀ k ≤ N, extW C.2.1 k = δ k) → (∀ k ≤ N, extL C.2.2 k = τ k) →
      (IsWalk E (extW C.2.1) (extL C.2.2) m ↔ IsWalk E δ τ m) ∧
      wt c (extW C.2.1) (extL C.2.2) m = wt c δ τ m ∧ (extW C.2.1 m = extW C.2.1 0 ↔ δ m = δ 0) := by
    intro m δ τ C hm hC h1 h2
    refine ⟨⟨fun hw k hk => ?_, fun hw k hk => ?_⟩, ?_, ?_⟩
    · have := hw k hk; rwa [h1 k (by omega), h1 (k + 1) (by omega), h2 k (by omega)] at this
    · rw [h1 k (by omega), h1 (k + 1) (by omega), h2 k (by omega)]; exact hw k hk
    · simp only [wt]
      apply Finset.sum_congr rfl
      intro k hk; rw [Finset.mem_range] at hk
      rw [h1 k (by omega), h1 (k + 1) (by omega), h2 k (by omega)]
    · rw [h1 m hm, h1 0 (by omega)]
  obtain ⟨C1, hC1, hC1a, hC1b⟩ := emb m1 δ1 τ1 hm1N
  have hC1S : C1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, valid]
    obtain ⟨t1, _, t3⟩ := transfer m1 δ1 τ1 C1 hm1N hC1 hC1a hC1b
    rw [hC1]; exact ⟨hm1, t1.2 hw1, t3.2 hc1⟩
  obtain ⟨Cs, hCsS, hmin⟩ := Finset.exists_min_image S mean ⟨C1, hC1S⟩
  have hCs := (Finset.mem_filter.1 hCsS).2
  refine ⟨mean Cs, ?_, ?_, ?_⟩
  · have h := hmin C1 hC1S
    have : mean C1 < 0 := by
      simp only [mean]
      obtain ⟨_, t2, _⟩ := transfer m1 δ1 τ1 C1 hm1N hC1 hC1a hC1b
      rw [hC1, t2]
      exact div_neg_of_neg_of_pos hneg1 (by exact_mod_cast hm1)
    linarith
  · apply closed_ge
    intro m δ τ hm hmN hw hc
    obtain ⟨C, hC, hCa, hCb⟩ := emb m δ τ hmN
    obtain ⟨t1, t2, t3⟩ := transfer m δ τ C hmN hC hCa hCb
    have hCS : C ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, valid]
      rw [hC]; exact ⟨hm, t1.2 hw, t3.2 hc⟩
    have h := hmin C hCS
    simp only [mean] at h
    rw [hC, t2] at h
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    rw [le_div_iff₀ hmpos] at h
    linarith
  · refine ⟨Cs.1, extW Cs.2.1, extL Cs.2.2, hCs.1, hCs.2.1, hCs.2.2, ?_⟩
    simp only [mean]
    have hmpos : (0 : ℝ) < (Cs.1 : ℕ) := by exact_mod_cast hCs.1
    field_simp

end MIGraph

open MIAux MIGraph

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

abbrev Arc (V A : Type*) := A ⊕ A ⊕ (V × V)

def Eaux (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) (u v : V) (e : Arc V A) : Prop :=
  AuxTailMSFP2 tail head e = u ∧ AuxHeadMSFP2 tail head e = v ∧
    AuxActiveMSFP2Z tail head cUpper cLower f xi e

def caux (tail head : A → V) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ)
    (_ _ : V) (e : Arc V A) : ℝ :=
  (AuxLengthMSFP2Z tail head gamma f xi e).untopD 0

lemma xm_eq_aux (z : V → ℤ) (u v : V) :
    (fun w => z w + (if w = v then (1:ℤ) else 0) - (if w = u then (1:ℤ) else 0)) = xm z u v := by
  funext w; simp only [xm, CharVec]; ring

lemma untopD_coe_eq (x : WithTop ℝ) (hx : x ≠ ⊤) : ((x.untopD 0 : ℝ) : WithTop ℝ) = x := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd rfl hx
  | coe a => rfl

lemma active_len_coe (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ)
    (hfz : f (BoundaryZ tail head xi) ≠ ⊤) (e : Arc V A)
    (he : AuxActiveMSFP2Z tail head cUpper cLower f xi e) :
    AuxLengthMSFP2Z tail head gamma f xi e =
      ((caux tail head gamma f xi (AuxTailMSFP2 tail head e) (AuxHeadMSFP2 tail head e) e : ℝ) : WithTop ℝ) := by
  refine (untopD_coe_eq _ ?_).symm
  rcases e with a | a | ⟨u, v⟩
  · exact WithTop.coe_ne_top
  · exact WithTop.coe_ne_top
  · simp only [AuxActiveMSFP2Z] at he
    simp only [AuxLengthMSFP2Z, DeltaF]
    obtain ⟨r0, hr0⟩ := WithTop.ne_top_iff_exists.1 hfz
    obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.1 he.2
    rw [← hr0, ← hr1]
    have hsub : (r1 : WithTop ℝ) - (r0 : WithTop ℝ) = ((r1 - r0 : ℝ) : WithTop ℝ) := by simp
    rw [hsub]
    exact WithTop.coe_ne_top

lemma cycleLength_eq_wt (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ)
    (hfz : f (BoundaryZ tail head xi) ≠ ⊤) (k : ℕ) (a : Fin (k + 1) → Arc V A)
    (hact : ∀ i, AuxActiveMSFP2Z tail head cUpper cLower f xi (a i)) :
    CycleLength (AuxLengthMSFP2Z tail head gamma f xi) k a =
      ((∑ i : Fin (k + 1),
        caux tail head gamma f xi (AuxTailMSFP2 tail head (a i)) (AuxHeadMSFP2 tail head (a i)) (a i) : ℝ) : WithTop ℝ) := by
  unfold CycleLength
  rw [Finset.sum_congr rfl (fun i _ => active_len_coe tail head cUpper cLower gamma f xi hfz (a i) (hact i))]
  push_cast
  rfl

lemma hasNeg_iff (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ)
    (hfz : f (BoundaryZ tail head xi) ≠ ⊤) :
    HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
      (AuxActiveMSFP2Z tail head cUpper cLower f xi) (AuxLengthMSFP2Z tail head gamma f xi) ↔
    ∃ m δ τ, IsWalk (Eaux tail head cUpper cLower f xi) δ τ m ∧ δ m = δ 0 ∧
      wt (caux tail head gamma f xi) δ τ m < 0 := by
  constructor
  · rintro ⟨k, a, hact, hcyc, hlt⟩
    rw [cycleLength_eq_wt tail head cUpper cLower gamma f xi hfz k a hact,
       ← WithTop.coe_zero, WithTop.coe_lt_coe] at hlt
    let δ : ℕ → V := fun j => AuxTailMSFP2 tail head (a ⟨j % (k + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
    let τ : ℕ → Arc V A := fun j => a ⟨j % (k + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    refine ⟨k + 1, δ, τ, ?_, ?_, ?_⟩
    · intro j hj
      have hjmod : j % (k + 1) = j := Nat.mod_eq_of_lt hj
      refine ⟨rfl, ?_, hact _⟩
      have h1 := hcyc ⟨j, hj⟩
      simp only [δ, τ]
      have hidx1 : (⟨j % (k + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (k + 1)) = ⟨j, hj⟩ := by
        ext; exact hjmod
      have hidx2 : (⟨(j + 1) % (k + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (k + 1)) =
          ⟨j, hj⟩ + 1 := by
        ext
        simp only [Fin.val_add_one]
        split_ifs with hlast
        · have hjk : j = k := congrArg Fin.val hlast
          subst hjk; simp [Nat.mod_self]
        · have : j + 1 < k + 1 := by
            have : j ≠ k := fun h => hlast (Fin.ext h)
            omega
          rw [Nat.mod_eq_of_lt this]
      rw [hidx1, hidx2, h1]
    · simp [δ, Nat.mod_self]
    · simp only [wt, caux]
      rw [← Fin.sum_univ_eq_sum_range]
      have hsum : (∑ i : Fin (k + 1), (AuxLengthMSFP2Z tail head gamma f xi (τ i)).untopD 0) =
          ∑ i : Fin (k + 1), (AuxLengthMSFP2Z tail head gamma f xi (a i)).untopD 0 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hi : (i : ℕ) % (k + 1) = i := Nat.mod_eq_of_lt i.isLt
        have hτ : τ i = a i := by
          dsimp [τ]
          congr 1
          ext
          exact hi
        rw [hτ]
      rw [hsum]
      exact hlt
  · rintro ⟨m, δ, τ, hw, hc, hlt⟩
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp [wt] at hlt
      · exact h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm)
    let a : Fin (k + 1) → Arc V A := fun i => τ i
    have hact : ∀ i, AuxActiveMSFP2Z tail head cUpper cLower f xi (a i) :=
      fun i => (hw i i.isLt).2.2
    refine ⟨k, a, hact, ?_, ?_⟩
    · intro i
      have h1 := (hw i i.isLt).2.1
      rw [h1]
      simp only [a, Fin.val_add_one]
      split_ifs with hl
      · have hik : (i : ℕ) + 1 = k + 1 := by rw [hl]; rfl
        rw [hik, hc, (hw 0 (Nat.succ_pos k)).1]
      · exact ((hw ((i : ℕ) + 1) (by
          have : (i : ℕ) ≠ k := fun h => hl (Fin.ext h)
          omega)).1).symm
    · rw [cycleLength_eq_wt tail head cUpper cLower gamma f xi hfz k a hact,
        ← WithTop.coe_zero, WithTop.coe_lt_coe]
      simp only [wt, caux] at hlt ⊢
      rw [← Fin.sum_univ_eq_sum_range] at hlt
      exact hlt

lemma bndZ_pair (tail head : A → V) (p : V → ℝ) (xi : A → ℤ) :
    L p (BoundaryZ tail head xi) = ∑ a : A, (p (tail a) - p (head a)) * (xi a : ℝ) := by
  have h1 : ∀ g : A → V, ∑ v : V, p v * ((∑ a ∈ Finset.univ.filter (fun a => g a = v), xi a : ℤ) : ℝ) =
      ∑ a : A, p (g a) * (xi a : ℝ) := by
    intro g
    push_cast
    simp only [Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [mul_ite]
  simp only [L, BoundaryZ, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, h1, sub_mul]

/-- Reverse direction: no negative cycle implies optimality. -/
theorem opt_of_no_neg (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (xi : A → ℤ)
    (hfeas : FeasibleFlowMSFP2Z tail head cUpper cLower f xi)
    (hno : ¬ HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
      (AuxActiveMSFP2Z tail head cUpper cLower f xi) (AuxLengthMSFP2Z tail head gamma f xi)) :
    OptimalFlowMSFP2Z tail head cUpper cLower gamma f xi := by
  refine ⟨hfeas, fun xi' hfeas' => ?_⟩
  by_cases hV : Nonempty V
  · haveI : Nonempty V := hV
    haveI : Nonempty (Arc V A) := ⟨.inr (.inr (Classical.arbitrary V, Classical.arbitrary V))⟩
    rw [hasNeg_iff tail head cUpper cLower gamma f xi hfeas.2] at hno
    have hnn : ∀ m δ τ, IsWalk (Eaux tail head cUpper cLower f xi) δ τ m → δ m = δ 0 →
        0 ≤ wt (caux tail head gamma f xi) δ τ m := by
      intro m δ τ hw hc
      by_contra hlt; push Not at hlt
      exact hno ⟨m, δ, τ, hw, hc, hlt⟩
    obtain ⟨π, hπ⟩ := potential hnn
    let z0 := BoundaryZ tail head xi
    let z' := BoundaryZ tail head xi'
    have hfz0 : f z0 ≠ ⊤ := hfeas.2
    have hfz' : f z' ≠ ⊤ := hfeas'.2
    obtain ⟨r0, hr0⟩ := WithTop.ne_top_iff_exists.1 hfz0
    obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.1 hfz'
    have harc : ∀ a : A, (gamma a + π (tail a) - π (head a)) * (xi a : ℝ) ≤
        (gamma a + π (tail a) - π (head a)) * (xi' a : ℝ) := by
      intro a
      rcases lt_trichotomy (xi a) (xi' a) with hlt | heq | hgt
      · have hact : AuxActiveMSFP2Z tail head cUpper cLower f xi (.inl a) := by
          show ((xi a : ℝ) : WithTop ℝ) < cUpper a
          exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by exact_mod_cast hlt)) (hfeas'.1 a).2
        have hp := hπ (tail a) (head a) (.inl a) ⟨rfl, rfl, hact⟩
        simp only [caux, AuxLengthMSFP2Z, WithTop.untopD_coe] at hp
        have hd : (0 : ℝ) ≤ (xi' a : ℝ) - (xi a : ℝ) := by
          have : (xi a : ℝ) ≤ (xi' a : ℝ) := by exact_mod_cast hlt.le
          linarith
        nlinarith
      · rw [heq]
      · have hact : AuxActiveMSFP2Z tail head cUpper cLower f xi (.inr (.inl a)) := by
          show cLower a < ((xi a : ℝ) : WithBot ℝ)
          exact lt_of_le_of_lt (hfeas'.1 a).1 (WithBot.coe_lt_coe.2 (by exact_mod_cast hgt))
        have hp := hπ (head a) (tail a) (.inr (.inl a)) ⟨rfl, rfl, hact⟩
        simp only [caux, AuxLengthMSFP2Z, WithTop.untopD_coe] at hp
        have hd : (xi' a : ℝ) - (xi a : ℝ) ≤ 0 := by
          have : (xi' a : ℝ) ≤ (xi a : ℝ) := by exact_mod_cast hgt.le
          linarith
        nlinarith
    have hloc : ∀ u v : V, pf f (-π) z0 ≤ pf f (-π) (xm z0 u v) := by
      intro u v
      by_cases huv : u = v
      · subst huv; rw [xm_self]
      by_cases htop : f (xm z0 u v) = ⊤
      · simp [pf, htop]
      obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.1 htop
      have hact : AuxActiveMSFP2Z tail head cUpper cLower f xi (.inr (.inr (u, v))) := by
        refine ⟨huv, ?_⟩
        rw [xm_eq_aux]; exact htop
      have hp := hπ u v (.inr (.inr (u, v))) ⟨rfl, rfl, hact⟩
      have hlen : caux tail head gamma f xi u v (.inr (.inr (u, v))) = r1 - r0 := by
        dsimp [caux, AuxLengthMSFP2Z, DeltaF]
        rw [xm_eq_aux]
        change ((f (xm z0 u v) - f z0).untopD 0) = r1 - r0
        rw [← hr1, ← hr0]
        have hsub : (r1 : WithTop ℝ) - (r0 : WithTop ℝ) = ((r1 - r0 : ℝ) : WithTop ℝ) := by simp
        rw [hsub, WithTop.untopD_coe]
      rw [hlen] at hp
      unfold pf
      rw [← hr0, ← hr1, L_xm, Pi.neg_apply, Pi.neg_apply, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_le_coe]
      linarith
    have hglob := LG (pf_exch f hf (-π)) z0 (by rw [pf_ne_top]; exact hfz0) hloc z'
    unfold pf at hglob
    rw [← hr0, ← hr', ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hglob
    simp only [L, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at hglob
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => harc a)
    have hb0 := bndZ_pair tail head π xi
    have hb' := bndZ_pair tail head π xi'
    simp only [L] at hb0 hb'
    have hsplit : ∀ x : A → ℤ, ∑ a : A, (gamma a + π (tail a) - π (head a)) * (x a : ℝ) =
        ∑ a : A, gamma a * (x a : ℝ) + ∑ a : A, (π (tail a) - π (head a)) * (x a : ℝ) := by
      intro x
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [hsplit xi, hsplit xi', ← hb0, ← hb'] at hsum
    unfold Gamma2Z
    change ((∑ a, gamma a * (xi a : ℝ) : ℝ) : WithTop ℝ) + f z0 ≤
      ((∑ a, gamma a * (xi' a : ℝ) : ℝ) : WithTop ℝ) + f z'
    rw [← hr0, ← hr', ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
    linarith
  · haveI : IsEmpty V := not_nonempty_iff.1 hV
    haveI : IsEmpty A := ⟨fun a => isEmptyElim (tail a)⟩
    have : xi = xi' := Subsingleton.elim _ _
    rw [this]

/-! ### Forward direction: optimality implies no negative cycle -/

def isC : Arc V A → Prop
  | .inr (.inr _) => True
  | _ => False

def undF : Arc V A → Option A
  | .inl a => some a
  | .inr (.inl a) => some a
  | .inr (.inr _) => none

def flowDelta : Arc V A → A → ℤ
  | .inl b => fun a => if a = b then 1 else 0
  | .inr (.inl b) => fun a => if a = b then -1 else 0
  | .inr (.inr _) => fun _ => 0

lemma bndZ_add (tail head : A → V) (xi d : A → ℤ) (v : V) :
    BoundaryZ tail head (fun a => xi a + d a) v =
      BoundaryZ tail head xi v + BoundaryZ tail head d v := by
  simp only [BoundaryZ, Finset.sum_add_distrib]; omega

lemma bndZ_sum {ι : Type*} (tail head : A → V) (s : Finset ι) (g : ι → A → ℤ) (v : V) :
    BoundaryZ tail head (fun a => ∑ i ∈ s, g i a) v =
      ∑ i ∈ s, BoundaryZ tail head (g i) v := by
  unfold BoundaryZ
  rw [Finset.sum_sub_distrib]
  congr 1 <;> exact Finset.sum_comm

lemma sum_ite_flow (g : A → V) (b : A) (c : ℤ) (v : V) :
    (∑ a ∈ Finset.univ.filter (fun a => g a = v), (if a = b then c else 0)) =
      if v = g b then c else 0 := by
  rw [Finset.sum_filter, Finset.sum_eq_single b]
  · by_cases h : g b = v
    · subst h; simp
    · have hv : v ≠ g b := Ne.symm h
      simp [h, hv]
  · intro a _ hab; simp [hab]
  · intro hb; exact absurd (Finset.mem_univ b) hb

lemma bndZ_flowDelta (tail head : A → V) (e : Arc V A) (he : ¬ isC e) (v : V) :
    BoundaryZ tail head (flowDelta e) v =
      CharVec (AuxTailMSFP2 tail head e) v - CharVec (AuxHeadMSFP2 tail head e) v := by
  rcases e with b | b | ⟨u1, u2⟩
  · dsimp only [BoundaryZ, flowDelta, AuxTailMSFP2, AuxHeadMSFP2, CharVec]
    rw [sum_ite_flow, sum_ite_flow]
  · dsimp only [BoundaryZ, flowDelta, AuxTailMSFP2, AuxHeadMSFP2, CharVec]
    rw [sum_ite_flow, sum_ite_flow]
    by_cases h1 : v = tail b <;> by_cases h2 : v = head b
    · rw [if_pos h1, if_pos h2, if_pos h2, if_pos h1]; rfl
    · rw [if_pos h1, if_neg h2, if_neg h2, if_pos h1]; rfl
    · rw [if_neg h1, if_pos h2, if_pos h2, if_neg h1]; rfl
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
  · exact absurd trivial he

lemma hfd_ne (e : Arc V A) (a : A) (hne : flowDelta e a ≠ 0) : undF e = some a := by
  rcases e with b | b | ⟨u1, v1⟩
  · simp only [flowDelta] at hne
    split_ifs at hne with h
    · subst h; rfl
    · exact absurd rfl hne
  · simp only [flowDelta] at hne
    split_ifs at hne with h
    · subst h; rfl
    · exact absurd rfl hne
  · simp [flowDelta] at hne

lemma cost_flowDelta (tail head : A → V) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ)
    (xi : A → ℤ) (π : V → ℝ) (e : Arc V A) (he : ¬ isC e) :
    ∑ a : A, (gamma a + π (tail a) - π (head a)) * (flowDelta e a : ℝ) =
      caux tail head gamma f xi (AuxTailMSFP2 tail head e) (AuxHeadMSFP2 tail head e) e +
        π (AuxTailMSFP2 tail head e) - π (AuxHeadMSFP2 tail head e) := by
  rcases e with b | b | ⟨u1, u2⟩
  · simp only [flowDelta, caux, AuxLengthMSFP2Z, AuxTailMSFP2, AuxHeadMSFP2, WithTop.untopD_coe]
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab; simp [hab]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · simp only [flowDelta, caux, AuxLengthMSFP2Z, AuxTailMSFP2, AuxHeadMSFP2, WithTop.untopD_coe]
    rw [Finset.sum_eq_single b]
    · simp; ring
    · intro a _ hab; simp [hab]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · exact absurd trivial he

theorem no_neg_of_opt (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hcU : ∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ))
    (hcL : ∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ)) (xi : A → ℤ)
    (hopt : OptimalFlowMSFP2Z tail head cUpper cLower gamma f xi) :
    ¬ HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
      (AuxActiveMSFP2Z tail head cUpper cLower f xi) (AuxLengthMSFP2Z tail head gamma f xi) := by
  obtain ⟨hfeas, hmin⟩ := hopt
  intro hneg
  have ⟨k0, a0, _, _, _⟩ := hneg
  haveI : Nonempty V := ⟨AuxTailMSFP2 tail head (a0 0)⟩
  haveI : Nonempty (Arc V A) := ⟨a0 0⟩
  rw [hasNeg_iff tail head cUpper cLower gamma f xi hfeas.2] at hneg
  obtain ⟨μ, hμ, hge, m1, δ1, τ1, hm1, hw1, hc1, hwt1⟩ := min_mean hneg
  let c' : V → V → Arc V A → ℝ := fun u v e => caux tail head gamma f xi u v e - μ
  have hnn' : ∀ m δ τ, IsWalk (Eaux tail head cUpper cLower f xi) δ τ m → δ m = δ 0 →
      0 ≤ wt c' δ τ m := by
    intro m δ τ hw hc
    have h := hge m δ τ hw hc
    simp only [wt, c'] at h ⊢
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith
  obtain ⟨π, hπ⟩ := potential hnn'
  let lr : Arc V A → ℝ := fun e =>
    caux tail head gamma f xi (AuxTailMSFP2 tail head e) (AuxHeadMSFP2 tail head e) e +
      π (AuxTailMSFP2 tail head e) - π (AuxHeadMSFP2 tail head e)
  have hlr : ∀ e, AuxActiveMSFP2Z tail head cUpper cLower f xi e → μ ≤ lr e := by
    intro e he
    have := hπ (AuxTailMSFP2 tail head e) (AuxHeadMSFP2 tail head e) e ⟨rfl, rfl, he⟩
    simp only [c', lr] at this ⊢; linarith
  let Tight : Arc V A → Prop := fun e =>
    AuxActiveMSFP2Z tail head cUpper cLower f xi e ∧ lr e = μ
  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ δ : ℕ → V, ∃ τ : ℕ → Arc V A,
    (∀ k < n, AuxTailMSFP2 tail head (τ k) = δ k ∧ AuxHeadMSFP2 tail head (τ k) = δ (k + 1) ∧
      Tight (τ k)) ∧ δ n = δ 0
  have hP : ∃ n, P n := by
    refine ⟨m1, hm1, δ1, τ1, ?_, hc1⟩
    have hsum0 : ∑ k ∈ Finset.range m1, (lr (τ1 k) - μ) = 0 := by
      have htel : ∑ k ∈ Finset.range m1, (π (δ1 k) - π (δ1 (k + 1))) = 0 := by
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        exact (shift_sum (fun k => π (δ1 k)) m1 (by rw [hc1])).symm
      have heq : ∑ k ∈ Finset.range m1, (lr (τ1 k) - μ) =
          wt (caux tail head gamma f xi) δ1 τ1 m1 - m1 * μ +
            ∑ k ∈ Finset.range m1, (π (δ1 k) - π (δ1 (k + 1))) := by
        have hlr_k : ∀ k ∈ Finset.range m1, lr (τ1 k) - μ =
            (caux tail head gamma f xi (δ1 k) (δ1 (k + 1)) (τ1 k) - μ) +
              (π (δ1 k) - π (δ1 (k + 1))) := by
          intro k hk
          rw [Finset.mem_range] at hk
          obtain ⟨ht, hh, _⟩ := hw1 k hk
          simp only [lr, ht, hh]; ring
        rw [Finset.sum_congr rfl hlr_k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rfl
      linarith
    have hnn_term : ∀ k ∈ Finset.range m1, 0 ≤ lr (τ1 k) - μ := by
      intro k hk; rw [Finset.mem_range] at hk
      linarith [hlr (τ1 k) (hw1 k hk).2.2]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn_term).1 hsum0
    intro k hk
    obtain ⟨ht, hh, ha⟩ := hw1 k hk
    exact ⟨ht, hh, ha, by linarith [hz k (Finset.mem_range.2 hk)]⟩
  obtain ⟨n0, ⟨hn0pos, δ0, τ0, hw0, hc0⟩, hfm⟩ : ∃ n0, P n0 ∧ ∀ m < n0, ¬ P m :=
    ⟨Nat.find hP, Nat.find_spec hP, fun m hm => Nat.find_min hP hm⟩
  let δ : ℕ → V := fun k => δ0 (k % n0)
  let τ : ℕ → Arc V A := fun k => τ0 (k % n0)
  have dmod : ∀ k, δ k = δ (k % n0) := fun k => by simp [δ, Nat.mod_mod]
  have tmod : ∀ k, τ k = τ (k % n0) := fun k => by simp [τ, Nat.mod_mod]
  have dper : ∀ k, δ (k + n0) = δ k := fun k => by simp [δ]
  have tper : ∀ k, τ (k + n0) = τ k := fun k => by simp [τ]
  have dlt : ∀ k < n0, δ k = δ0 k := fun k hk => by simp [δ, Nat.mod_eq_of_lt hk]
  have tlt : ∀ k < n0, τ k = τ0 k := fun k hk => by simp [τ, Nat.mod_eq_of_lt hk]
  have dsucc : ∀ k, δ (k + 1) = δ (k % n0 + 1) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k n0, Nat.add_right_comm]
    exact per_mul δ n0 dper _ _
  have step : ∀ k, AuxTailMSFP2 tail head (τ k) = δ k ∧
      AuxHeadMSFP2 tail head (τ k) = δ (k + 1) ∧ Tight (τ k) := by
    intro k
    rw [tmod k, dmod k, dsucc k]
    have hr := Nat.mod_lt k hn0pos
    rw [tlt _ hr, dlt _ hr]
    obtain ⟨h1, h2, h3⟩ := hw0 (k % n0) hr
    refine ⟨h1, ?_, h3⟩
    by_cases hr1 : k % n0 + 1 = n0
    · have hdn0 : δ (k % n0 + 1) = δ0 (k % n0 + 1) := by
        rw [hr1]
        have h0 := dper 0
        rw [Nat.zero_add] at h0
        rw [h0, dlt 0 hn0pos, hc0]
      rw [hdn0]
      exact h2
    · rw [dlt _ (by omega)]; exact h2
  have inj : ∀ a b, a < n0 → b < n0 → δ a = δ b → a = b := by
    intro a b ha hb he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · apply hfm (b - a) (by omega)
      refine ⟨by omega, fun k => δ (a + k), fun k => τ (a + k), fun k hk => ?_, ?_⟩
      · simp only [show a + (k + 1) = a + k + 1 by omega]; exact step _
      · simp only [Nat.add_zero, show a + (b - a) = b by omega, he]
    · apply hfm (a - b) (by omega)
      refine ⟨by omega, fun k => δ (b + k), fun k => τ (b + k), fun k hk => ?_, ?_⟩
      · simp only [show b + (k + 1) = b + k + 1 by omega]; exact step _
      · simp only [Nat.add_zero, show b + (a - b) = a by omega, he]
  have inj' : ∀ a b, δ a = δ b → a % n0 = b % n0 := by
    intro a b he
    rw [dmod a, dmod b] at he
    exact inj _ _ (Nat.mod_lt _ hn0pos) (Nat.mod_lt _ hn0pos) he
  let z0 := BoundaryZ tail head xi
  have hfz0 : f z0 ≠ ⊤ := hfeas.2
  obtain ⟨r0, hr0⟩ := WithTop.ne_top_iff_exists.1 hfz0
  set g := pf f (-π)
  have hg : MExchangeAxiom g := pf_exch f hf (-π)
  set α0 : ℝ := r0 + L (-π) z0
  have hx0 : g z0 = (α0 : WithTop ℝ) := by
    unfold g pf α0
    rw [← hr0, WithTop.coe_add]
  have hC_iff : ∀ u v : V, Tight (.inr (.inr (u, v))) ↔
      u ≠ v ∧ g (xm z0 u v) = ((α0 + μ : ℝ) : WithTop ℝ) := by
    intro u v
    constructor
    · rintro ⟨⟨huv, hne⟩, hlr_eq⟩
      refine ⟨huv, ?_⟩
      rw [xm_eq_aux] at hne
      change f (xm z0 u v) ≠ ⊤ at hne
      obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.1 hne
      have hlen : lr (.inr (.inr (u, v))) = r1 - r0 + π u - π v := by
        dsimp [lr, caux, AuxTailMSFP2, AuxHeadMSFP2, AuxLengthMSFP2Z, DeltaF]
        rw [xm_eq_aux]
        change ((f (xm z0 u v) - f z0).untopD 0) + π u - π v = r1 - r0 + π u - π v
        rw [← hr1, ← hr0]
        have hsub : (r1 : WithTop ℝ) - (r0 : WithTop ℝ) = ((r1 - r0 : ℝ) : WithTop ℝ) := by simp
        rw [hsub, WithTop.untopD_coe]
      rw [hlen] at hlr_eq
      unfold g pf α0
      rw [← hr1, L_xm, Pi.neg_apply, Pi.neg_apply, ← WithTop.coe_add, WithTop.coe_eq_coe]
      linarith
    · rintro ⟨huv, hg_eq⟩
      have hne : f (xm z0 u v) ≠ ⊤ := by
        intro ht
        have : g (xm z0 u v) = ⊤ := by simp [g, pf, ht]
        rw [this] at hg_eq
        exact WithTop.top_ne_coe hg_eq
      obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.1 hne
      refine ⟨⟨huv, by rw [xm_eq_aux]; exact hne⟩, ?_⟩
      unfold g pf α0 at hg_eq
      rw [← hr1, L_xm, Pi.neg_apply, Pi.neg_apply, ← WithTop.coe_add, WithTop.coe_eq_coe] at hg_eq
      dsimp [lr, caux, AuxTailMSFP2, AuxHeadMSFP2, AuxLengthMSFP2Z, DeltaF]
      rw [xm_eq_aux]
      change ((f (xm z0 u v) - f z0).untopD 0) + π u - π v = μ
      rw [← hr1, ← hr0]
      have hsub : (r1 : WithTop ℝ) - (r0 : WithTop ℝ) = ((r1 - r0 : ℝ) : WithTop ℝ) := by simp
      rw [hsub, WithTop.untopD_coe]
      linarith
  have hC_ge : ∀ u v : V, u ≠ v → ((α0 + μ : ℝ) : WithTop ℝ) ≤ g (xm z0 u v) := by
    intro u v huv
    by_cases hne : f (xm z0 u v) = ⊤
    · simp [g, pf, hne]
    obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.1 hne
    have hact : AuxActiveMSFP2Z tail head cUpper cLower f xi (.inr (.inr (u, v))) :=
      ⟨huv, by rw [xm_eq_aux]; exact hne⟩
    have hle := hlr (.inr (.inr (u, v))) hact
    have hlen : lr (.inr (.inr (u, v))) = r1 - r0 + π u - π v := by
      dsimp [lr, caux, AuxTailMSFP2, AuxHeadMSFP2, AuxLengthMSFP2Z, DeltaF]
      rw [xm_eq_aux]
      change ((f (xm z0 u v) - f z0).untopD 0) + π u - π v = r1 - r0 + π u - π v
      rw [← hr1, ← hr0]
      have hsub : (r1 : WithTop ℝ) - (r0 : WithTop ℝ) = ((r1 - r0 : ℝ) : WithTop ℝ) := by simp
      rw [hsub, WithTop.untopD_coe]
    rw [hlen] at hle
    unfold g pf α0
    rw [← hr1, L_xm, Pi.neg_apply, Pi.neg_apply, ← WithTop.coe_add, WithTop.coe_le_coe]
    linarith
  have isC_eq : ∀ k, isC (τ k) → τ k = .inr (.inr (δ k, δ (k + 1))) := by
    intro k hk
    obtain ⟨ht, hh, _⟩ := step k
    rcases hτ : τ k with a | a | ⟨u, v⟩
    · rw [hτ] at hk; exact absurd hk id
    · rw [hτ] at hk; exact absurd hk id
    · rw [hτ] at ht hh
      simp only [AuxTailMSFP2, AuxHeadMSFP2] at ht hh
      rw [ht, hh]
  have noTT : ∀ k, isC (τ k) → ¬ isC (τ (k + 1)) := by
    intro k h1 h2
    have e1 := isC_eq k h1
    have e2 := isC_eq (k + 1) h2
    have t1 := (step k).2.2
    have t2 := (step (k + 1)).2.2
    rw [e1, hC_iff] at t1
    rw [e2, hC_iff] at t2
    have ht := tri hg z0 α0 hx0 (δ k) (δ (k + 1)) (δ (k + 1 + 1)) t1.1 t2.1
    rw [t1.2, t2.2] at ht
    by_cases hac : δ k = δ (k + 1 + 1)
    · rw [← hac, xm_self, hx0, coe_add2, coe_add2, WithTop.coe_le_coe] at ht; linarith
    · have hl := hC_ge (δ k) (δ (k + 1 + 1)) hac
      induction hA : g (xm z0 (δ k) (δ (k + 1 + 1))) using WithTop.recTopCoe with
      | top => rw [hA] at ht; simp at ht
      | coe A =>
        rw [hA] at ht hl
        rw [coe_add2, coe_add2, WithTop.coe_le_coe] at ht
        rw [WithTop.coe_le_coe] at hl; linarith
  have chord : ∀ i j, Tight (.inr (.inr (δ i, δ j))) → δ j = δ (i + 1) := by
    intro i j hT
    obtain ⟨i', hi'⟩ : ∃ i', i % n0 = i' := ⟨_, rfl⟩
    obtain ⟨j', hj'⟩ : ∃ j', j % n0 = j' := ⟨_, rfl⟩
    have hi'lt : i' < n0 := hi' ▸ Nat.mod_lt _ hn0pos
    have hj'lt : j' < n0 := hj' ▸ Nat.mod_lt _ hn0pos
    rw [dmod i, dmod j, hi', hj'] at hT
    rw [dmod j, dsucc i, hi', hj']
    by_contra hne
    obtain ⟨m, hm⟩ : ∃ m, m = if j' ≤ i' then i' - j' + 1 else i' + n0 - j' + 1 := ⟨_, rfl⟩
    have hmpos : 0 < m := by
      by_cases hc : j' ≤ i'
      · rw [if_pos hc] at hm; omega
      · rw [if_neg hc] at hm; omega
    have hjm : δ (j' + (m - 1)) = δ i' := by
      by_cases hc : j' ≤ i'
      · rw [if_pos hc] at hm; rw [hm, show j' + (i' - j' + 1 - 1) = i' by omega]
      · rw [if_neg hc] at hm
        rw [hm, show j' + (i' + n0 - j' + 1 - 1) = i' + n0 by omega, dper]
    have hmlt : m < n0 := by
      by_contra hge
      apply hne
      by_cases hc : j' ≤ i'
      · rw [if_pos hc] at hm
        rw [show j' = 0 by omega, show i' + 1 = 0 + n0 by omega, dper]
      · rw [if_neg hc] at hm
        rw [show j' = i' + 1 by omega]
    apply hfm m hmlt
    refine ⟨hmpos, fun k => if k = m then δ j' else δ (j' + k),
      fun k => if k + 1 = m then .inr (.inr (δ i', δ j')) else τ (j' + k), fun k hk => ?_, ?_⟩
    · simp only [if_neg (show k ≠ m by omega)]
      by_cases hk1 : k + 1 = m
      · simp only [if_pos hk1]
        rw [show k = m - 1 by omega, hjm]
        exact ⟨rfl, rfl, hT⟩
      · simp only [if_neg hk1, show j' + (k + 1) = j' + k + 1 by omega]; exact step _
    · dsimp only; rw [if_pos rfl, if_neg (show (0 : ℕ) ≠ m by omega), Nat.add_zero]
  set IC := (Finset.range n0).filter (fun i => isC (τ i))
  set IF := (Finset.range n0).filter (fun i => ¬ isC (τ i))
  have memIC : ∀ i, i ∈ IC ↔ i < n0 ∧ isC (τ i) := by intro i; simp [IC]
  have memIF : ∀ i, i ∈ IF ↔ i < n0 ∧ ¬ isC (τ i) := by intro i; simp [IF]
  have hv1 : ∀ i ∈ IC, ∀ j ∈ IC, i ≠ j → δ (i + 1) ≠ δ (j + 1) := by
    intro i hi j hj hij he
    have := inj' _ _ he
    rw [mod_succ _ _ hn0pos, mod_succ _ _ hn0pos, Nat.mod_eq_of_lt ((memIC i).1 hi).1,
      Nat.mod_eq_of_lt ((memIC j).1 hj).1] at this
    have := ((memIC i).1 hi).1; have := ((memIC j).1 hj).1
    split_ifs at * <;> omega
  have huv1 : ∀ i ∈ IC, ∀ j ∈ IC, δ i ≠ δ (j + 1) := by
    intro i hi j hj he
    have hmod := inj' i (j + 1) he
    have h1 := ((memIC i).1 hi).2
    rw [tmod i, hmod, ← tmod (j + 1)] at h1
    exact noTT j ((memIC j).1 hj).2 h1
  have M1 := ML hg (fun k => δ k) (fun k => δ (k + 1)) μ IC z0 α0 hx0
    (fun i hi j hj hij he => hij (inj i j ((memIC i).1 hi).1 ((memIC j).1 hj).1 he)) hv1 huv1
    (fun i hi => by
      have h1 := (step i).2.2
      rw [isC_eq i ((memIC i).1 hi).2, hC_iff] at h1
      exact h1.2)
    (fun i hi j hj hij => lt_of_le_of_ne (hC_ge _ _ (huv1 i hi j hj)) (fun he =>
      hv1 i hi j hj hij (chord i (j + 1) ((hC_iff _ _).2 ⟨huv1 i hi j hj, he.symm⟩)).symm))
  -- Now construct the augmented flow xi'
  set xi' : A → ℤ := fun a => xi a + ∑ i ∈ IF, flowDelta (τ i) a
  have hund_inj : ∀ i ∈ IF, ∀ j ∈ IF, i ≠ j → undF (τ i) ≠ undF (τ j) := by
    intro i hi j hj hij heq
    have hiF := ((memIF i).1 hi).2
    have hjF := ((memIF j).1 hj).2
    have hiT := (step i).2.2
    have hjT := (step j).2.2
    rcases hti : τ i with ai | ai | ⟨u1, v1⟩
    · rcases htj : τ j with aj | aj | ⟨u2, v2⟩
      · rw [hti, htj] at heq; simp only [undF, Option.some.injEq] at heq; subst heq
        have h1 := (step i).1; have h2 := (step j).1
        rw [hti, AuxTailMSFP2] at h1; rw [htj, AuxTailMSFP2] at h2
        exact hij (inj i j ((memIF i).1 hi).1 ((memIF j).1 hj).1 (h1.symm.trans h2))
      · rw [hti, htj] at heq; simp only [undF, Option.some.injEq] at heq; subst heq
        have l1 := hiT.2; have l2 := hjT.2
        rw [hti] at l1; rw [htj] at l2
        simp only [lr, caux, AuxTailMSFP2, AuxHeadMSFP2, AuxLengthMSFP2Z, WithTop.untopD_coe] at l1 l2
        linarith
      · rw [htj] at hjF; exact absurd trivial hjF
    · rcases htj : τ j with aj | aj | ⟨u2, v2⟩
      · rw [hti, htj] at heq; simp only [undF, Option.some.injEq] at heq; subst heq
        have l1 := hiT.2; have l2 := hjT.2
        rw [hti] at l1; rw [htj] at l2
        simp only [lr, caux, AuxTailMSFP2, AuxHeadMSFP2, AuxLengthMSFP2Z, WithTop.untopD_coe] at l1 l2
        linarith
      · rw [hti, htj] at heq; simp only [undF, Option.some.injEq] at heq; subst heq
        have h1 := (step i).1; have h2 := (step j).1
        rw [hti, AuxTailMSFP2] at h1; rw [htj, AuxTailMSFP2] at h2
        exact hij (inj i j ((memIF i).1 hi).1 ((memIF j).1 hj).1 (h1.symm.trans h2))
      · rw [htj] at hjF; exact absurd trivial hjF
    · rw [hti] at hiF; exact absurd trivial hiF
  have hbox' : ∀ a : A, cLower a ≤ ((xi' a : ℝ) : WithBot ℝ) ∧ ((xi' a : ℝ) : WithTop ℝ) ≤ cUpper a := by
    intro a
    by_cases hex : ∃ i ∈ IF, flowDelta (τ i) a ≠ 0
    · obtain ⟨i, hi, hne⟩ := hex
      have hsum_single : ∑ j ∈ IF, flowDelta (τ j) a = flowDelta (τ i) a := by
        rw [Finset.sum_eq_single i]
        · intro j hj hji
          by_contra hne'
          exact hund_inj j hj i hi hji ((hfd_ne _ a hne').trans (hfd_ne _ a hne).symm)
        · intro h; exact absurd hi h
      have hxia : xi' a = xi a + flowDelta (τ i) a := by simp only [xi', hsum_single]
      have hact := (step i).2.2.1
      have h1 := hfd_ne (τ i) a hne
      rcases hti : τ i with b | b | ⟨u1, v1⟩
      · rw [hti] at h1 hact hxia
        simp only [undF, Option.some.injEq] at h1; subst h1
        simp only [flowDelta, if_true] at hxia
        simp only [AuxActiveMSFP2Z] at hact
        rw [hxia]; push_cast
        refine ⟨(hfeas.1 b).1.trans (WithBot.coe_le_coe.2 (by linarith)), ?_⟩
        rcases hcU b with htop | ⟨n, hn⟩
        · rw [htop]; exact le_top
        · rw [hn] at hact ⊢
          rw [WithTop.coe_lt_coe] at hact
          have h1 : xi b < n := by exact_mod_cast hact
          have h2 : xi b + 1 ≤ n := by omega
          have h3 : (xi b : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h2
          exact WithTop.coe_le_coe.2 h3
      · rw [hti] at h1 hact hxia
        simp only [undF, Option.some.injEq] at h1; subst h1
        simp only [flowDelta, if_true] at hxia
        simp only [AuxActiveMSFP2Z] at hact
        rw [hxia]; push_cast
        refine ⟨?_, (WithTop.coe_le_coe.2 (by linarith)).trans (hfeas.1 b).2⟩
        rcases hcL b with hbot | ⟨n, hn⟩
        · rw [hbot]; exact bot_le
        · rw [hn] at hact ⊢
          rw [WithBot.coe_lt_coe] at hact
          have h1 : n < xi b := by exact_mod_cast hact
          have h2 : n ≤ xi b + -1 := by omega
          have h3 : (n : ℝ) ≤ (xi b : ℝ) + -1 := by exact_mod_cast h2
          exact WithBot.coe_le_coe.2 h3
      · rw [hti] at h1; simp [undF] at h1
    · push Not at hex
      have hxia : xi' a = xi a := by
        simp only [xi', Finset.sum_eq_zero hex, add_zero]
      rw [hxia]; exact hfeas.1 a
  have hbnd' : BoundaryZ tail head xi' = bulk (fun k => δ k) (fun k => δ (k + 1)) z0 IC := by
    funext v
    rw [bndZ_add, bndZ_sum]
    simp only [bulk]
    have hstep_v : ∀ i ∈ IF, BoundaryZ tail head (flowDelta (τ i)) v =
        CharVec (δ i) v - CharVec (δ (i + 1)) v := by
      intro i hi
      rw [bndZ_flowDelta tail head (τ i) ((memIF i).1 hi).2 v, (step i).1, (step i).2.1]
    rw [Finset.sum_congr rfl hstep_v]
    have htot : ∑ i ∈ Finset.range n0, (CharVec (δ i) v - CharVec (δ (i + 1)) v) = 0 := by
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact (shift_sum (fun i => CharVec (δ i) v) n0 (by simp [δ, hc0])).symm
    have hsplit : ∑ i ∈ Finset.range n0, (CharVec (δ i) v - CharVec (δ (i + 1)) v) =
        ∑ i ∈ IC, (CharVec (δ i) v - CharVec (δ (i + 1)) v) +
        ∑ i ∈ IF, (CharVec (δ i) v - CharVec (δ (i + 1)) v) :=
      (Finset.sum_filter_add_sum_filter_not (Finset.range n0) (fun i => isC (τ i)) _).symm
    dsimp only [z0]
    omega
  rw [← hbnd'] at M1
  have hfz' : f (BoundaryZ tail head xi') ≠ ⊤ := by
    intro ht
    have hgtop : g (BoundaryZ tail head xi') = ⊤ := by simp [g, pf, ht]
    rw [hgtop] at M1
    exact not_top_lt (lt_of_le_of_lt M1 (WithTop.coe_lt_top _))
  obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.1 hfz'
  have hfeas' : FeasibleFlowMSFP2Z tail head cUpper cLower f xi' := ⟨hbox', hfz'⟩
  have hM1' : r' + L (-π) (BoundaryZ tail head xi') ≤ α0 + IC.card * μ := by
    simp only [g, pf, ← hr', ← WithTop.coe_add, WithTop.coe_le_coe] at M1
    exact M1
  have hflow_cost : ∑ a : A, (gamma a + π (tail a) - π (head a)) * ((xi' a : ℝ) - (xi a : ℝ)) =
      IF.card * μ := by
    have hsub : ∀ a : A, (xi' a : ℝ) - (xi a : ℝ) = ∑ i ∈ IF, (flowDelta (τ i) a : ℝ) := by
      intro a; simp only [xi']; push_cast; ring
    simp_rw [hsub, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ i ∈ IF, ∑ a : A, (gamma a + π (tail a) - π (head a)) * (flowDelta (τ i) a : ℝ) = μ := by
      intro i hi
      rw [cost_flowDelta tail head gamma f xi π (τ i) ((memIF i).1 hi).2]
      exact (step i).2.2.2
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hb0 := bndZ_pair tail head π xi
  have hb' := bndZ_pair tail head π xi'
  have hLn0 : L (-π) z0 = - L π z0 := by simp [L, Finset.sum_neg_distrib]
  have hLn' : L (-π) (BoundaryZ tail head xi') = - L π (BoundaryZ tail head xi') := by
    simp [L, Finset.sum_neg_distrib]
  have hflow_split : ∑ a : A, (gamma a + π (tail a) - π (head a)) * ((xi' a : ℝ) - (xi a : ℝ)) =
      (∑ a : A, gamma a * (xi' a : ℝ) - ∑ a : A, gamma a * (xi a : ℝ)) +
      (L π (BoundaryZ tail head xi') - L π z0) := by
    rw [hb0, hb', ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hcards : (IC.card : ℝ) + (IF.card : ℝ) = n0 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range n0) (p := fun i => isC (τ i))
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hopt_le := hmin xi' hfeas'
  unfold Gamma2Z at hopt_le
  change ((∑ a, gamma a * (xi a : ℝ) : ℝ) : WithTop ℝ) + f z0 ≤
    ((∑ a, gamma a * (xi' a : ℝ) : ℝ) : WithTop ℝ) + f (BoundaryZ tail head xi') at hopt_le
  rw [← hr0, ← hr', ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hopt_le
  dsimp only [α0] at hM1'
  have hcards_mu : (IC.card : ℝ) * μ + (IF.card : ℝ) * μ = (n0 : ℝ) * μ := by
    rw [← add_mul, hcards]
  have hn0_pos : (0 : ℝ) < n0 := by exact_mod_cast hn0pos
  have hn0_neg : (n0 : ℝ) * μ < 0 := mul_neg_of_pos_of_neg hn0_pos hμ
  linarith

end P25a32c21

theorem solution {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hcU : ∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ))
    (hcL : ∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ)) (xi : A → ℤ)
    (hfeas : FeasibleFlowMSFP2Z tail head cUpper cLower f xi) :
    OptimalFlowMSFP2Z tail head cUpper cLower gamma f xi ↔
      ¬ HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
        (AuxActiveMSFP2Z tail head cUpper cLower f xi) (AuxLengthMSFP2Z tail head gamma f xi) :=
  ⟨P25a32c21.no_neg_of_opt tail head cUpper cLower gamma f hf hcU hcL xi,
   P25a32c21.opt_of_no_neg tail head cUpper cLower gamma f hf xi hfeas⟩
