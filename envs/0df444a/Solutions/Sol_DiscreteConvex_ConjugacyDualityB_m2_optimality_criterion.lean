-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.m2_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T19:30:18.996957+00:00
-- url     : https://prove2.me/submissions/b3dd0b95-c4c5-4018-a31e-92168d518931

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex


open DiscreteConvex.MConvexFunctions

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace MIAux

variable {W : Type*} [Fintype W] [DecidableEq W]

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

/-! ### WithTop real arithmetic helpers -/

lemma wt_cancel {A B : WithTop ℝ} {a c : ℝ} (h : (a : WithTop ℝ) + A ≤ B + c) (hca : c ≤ a) :
    A ≤ B := by
  induction A using WithTop.recTopCoe with
  | top => simp at h; subst h; simp
  | coe A =>
    induction B using WithTop.recTopCoe with
    | top => simp
    | coe B =>
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
      rw [WithTop.coe_le_coe]; linarith

/-! ### Matching lemma -/

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

lemma sub_le_of {Z : WithTop ℝ} {a s : ℝ} (h : (s : WithTop ℝ) ≤ Z + (a : WithTop ℝ)) :
    ((s - a : ℝ) : WithTop ℝ) ≤ Z := by
  induction Z using WithTop.recTopCoe with
  | top => simp
  | coe Z => rw [← WithTop.coe_add, WithTop.coe_le_coe] at h; rw [WithTop.coe_le_coe]; linarith


lemma coe_add2 (a b : ℝ) : (a : WithTop ℝ) + (b : WithTop ℝ) = ((a + b : ℝ) : WithTop ℝ) :=
  (WithTop.coe_add a b).symm

/-- diagonal upper bound -/
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

/-- lower bound at the shifted point -/
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

end MIAux


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

/-- lower bound for closed walks from the short ones -/
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

/-- walks are bounded below when there is no negative closed walk -/
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

/-- potentials from the absence of negative closed walks -/
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

/-- the minimum mean closed walk -/
lemma min_mean [Fintype L] [DecidableEq L]
    (hneg : ∃ m δ τ, IsWalk E δ τ m ∧ δ m = δ 0 ∧ wt c δ τ m < 0) :
    ∃ μ : ℝ, μ < 0 ∧ (∀ m δ τ, IsWalk E δ τ m → δ m = δ 0 → (m : ℝ) * μ ≤ wt c δ τ m) ∧
      ∃ m δ τ, 0 < m ∧ IsWalk E δ τ m ∧ δ m = δ 0 ∧ wt c δ τ m = m * μ := by
  classical
  set N := Fintype.card W
  -- a short negative closed walk
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
  -- embedding of a short walk
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


open DiscreteConvex.MConvexFunctions

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace MIAux

variable {W : Type*} [Fintype W] [DecidableEq W]

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

def ind (Y : Finset W) : W → ℤ := fun w => if w ∈ Y then 1 else 0

lemma sum_char_eq (T : Finset W) (w : W) : ∑ y ∈ T, CharVec y w = ind T w := by
  simp only [CharVec, ind]
  exact Finset.sum_ite_eq T w (fun _ => (1 : ℤ))

lemma bulk_eq (u v : ℕ → W) (s : Finset ℕ) (x : W → ℤ)
    (hu : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → u i ≠ u j) (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i ≠ v j) :
    bulk u v x s = fun w => x w + ind (s.image v) w - ind (s.image u) w := by
  funext w
  simp only [bulk, Finset.sum_sub_distrib]
  rw [← sum_char_eq, ← sum_char_eq, Finset.sum_image, Finset.sum_image]
  · ring
  · intro i hi j hj he; by_contra hne; exact hu i hi j hj hne he
  · intro i hi j hj he; by_contra hne; exact hv i hi j hj hne he

lemma card_img (u : ℕ → W) (s : Finset ℕ) (hu : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → u i ≠ u j) :
    (s.image u).card = s.card :=
  Finset.card_image_of_injOn (fun i hi j hj he => by
    by_contra hne; exact hu i hi j hj hne he)

theorem core2 {h1 h2 : (W → ℤ) → WithTop ℝ} (hg1 : MExchangeAxiom h1) (hg2 : MExchangeAxiom h2)
    (x : W → ℤ) (α1 α2 μ : ℝ) (hx1 : h1 x = α1) (hx2 : h2 x = α2) (hμ : μ < 0)
    (hmin : ∀ Y Z : Finset W, Y.card = Z.card → ((α1 + α2 : ℝ) : WithTop ℝ) ≤
      h1 (fun w => x w + ind Y w - ind Z w) + h2 (fun w => x w + ind Y w - ind Z w))
    (L1 : ∀ a b, a ≠ b → ((α1 + μ : ℝ) : WithTop ℝ) ≤ h1 (xm x a b))
    (L2 : ∀ a b, a ≠ b → ((α2 + μ : ℝ) : WithTop ℝ) ≤ h2 (xm x b a))
    (hwalk : ∃ n, ∃ γ : ℕ → W, 0 < n ∧ (∀ k < n,
      (γ k ≠ γ (k + 1) ∧ h1 (xm x (γ k) (γ (k + 1))) = ((α1 + μ : ℝ) : WithTop ℝ)) ∨
      (γ k ≠ γ (k + 1) ∧ h2 (xm x (γ (k + 1)) (γ k)) = ((α2 + μ : ℝ) : WithTop ℝ))) ∧ γ n = γ 0) :
    False := by
  classical
  let T1 : W → W → Prop := fun a b => a ≠ b ∧ h1 (xm x a b) = ((α1 + μ : ℝ) : WithTop ℝ)
  let T2 : W → W → Prop := fun a b => a ≠ b ∧ h2 (xm x b a) = ((α2 + μ : ℝ) : WithTop ℝ)
  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ γ : ℕ → W,
    (∀ k < n, T1 (γ k) (γ (k + 1)) ∨ T2 (γ k) (γ (k + 1))) ∧ γ n = γ 0
  have hP : ∃ n, P n := by
    obtain ⟨n, γ, hn, hw, hc⟩ := hwalk
    exact ⟨n, hn, γ, hw, hc⟩
  obtain ⟨n0, ⟨hn0pos, γ0, hw0, hc0⟩, hfm⟩ : ∃ n0, P n0 ∧ ∀ m, m < n0 → ¬ P m :=
    ⟨Nat.find hP, Nat.find_spec hP, fun m hm => Nat.find_min hP hm⟩
  let γ : ℕ → W := fun k => γ0 (k % n0)
  have gmod : ∀ k, γ k = γ (k % n0) := fun k => by simp [γ, Nat.mod_mod]
  have per : ∀ k, γ (k + n0) = γ k := fun k => by simp [γ]
  have glt : ∀ k, k < n0 → γ k = γ0 k := fun k hk => by simp [γ, Nat.mod_eq_of_lt hk]
  have gsucc : ∀ k, γ (k + 1) = γ (k % n0 + 1) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k n0, Nat.add_right_comm]
    exact per_mul γ n0 per _ _
  have tight : ∀ k, T1 (γ k) (γ (k + 1)) ∨ T2 (γ k) (γ (k + 1)) := by
    intro k
    rw [gmod k, gsucc k]
    have hr := Nat.mod_lt k hn0pos
    rw [glt _ hr]
    by_cases hr1 : k % n0 + 1 = n0
    · have e : γ (k % n0 + 1) = γ0 0 := by rw [hr1, ← glt 0 hn0pos, ← per 0, Nat.zero_add]
      rw [e]
      have := hw0 (k % n0) hr
      rwa [hr1, hc0] at this
    · rw [glt _ (by omega)]; exact hw0 _ hr
  -- injectivity on one period
  have inj : ∀ a b, a < n0 → b < n0 → γ a = γ b → a = b := by
    intro a b ha hb he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · apply hfm (b - a) (by omega)
      refine ⟨by omega, fun k => γ (a + k), fun k hk => ?_, ?_⟩
      · simp only [show a + (k + 1) = a + k + 1 by omega]; exact tight _
      · simp only [Nat.add_zero, show a + (b - a) = b by omega, he]
    · apply hfm (a - b) (by omega)
      refine ⟨by omega, fun k => γ (b + k), fun k hk => ?_, ?_⟩
      · simp only [show b + (k + 1) = b + k + 1 by omega]; exact tight _
      · simp only [Nat.add_zero, show b + (a - b) = a by omega, he]
  have inj' : ∀ a b, γ a = γ b → a % n0 = b % n0 := by
    intro a b he
    rw [gmod a, gmod b] at he
    exact inj _ _ (Nat.mod_lt _ hn0pos) (Nat.mod_lt _ hn0pos) he
  have hn2 : 2 ≤ n0 := by
    by_contra hh
    have h1' : n0 = 1 := by omega
    have := tight 0
    have e : γ (0 + 1) = γ 0 := by rw [gmod (0 + 1), h1']
    rw [e] at this
    rcases this with h | h <;> exact h.1 rfl
  -- no two consecutive arcs of the same type
  have noTT1 : ∀ a b c, T1 a b → T1 b c → False := by
    intro a b c hab hbc
    have ht := tri hg1 x α1 hx1 a b c hab.1 hbc.1
    rw [hab.2, hbc.2] at ht
    by_cases hac : a = c
    · subst hac
      rw [xm_self, hx1, coe_add2, coe_add2, WithTop.coe_le_coe] at ht; linarith
    · have hl := L1 a c hac
      induction hA : h1 (xm x a c) using WithTop.recTopCoe with
      | top => rw [hA] at ht; simp at ht
      | coe A =>
        rw [hA] at ht hl
        rw [coe_add2, coe_add2, WithTop.coe_le_coe] at ht
        rw [WithTop.coe_le_coe] at hl; linarith
  have noTT2 : ∀ a b c, T2 a b → T2 b c → False := by
    intro a b c hab hbc
    have ht := tri hg2 x α2 hx2 c b a hbc.1.symm hab.1.symm
    rw [hab.2, hbc.2] at ht
    by_cases hac : c = a
    · subst hac
      rw [xm_self, hx2, coe_add2, coe_add2, WithTop.coe_le_coe] at ht; linarith
    · have hl := L2 a c (Ne.symm hac)
      induction hA : h2 (xm x c a) using WithTop.recTopCoe with
      | top => rw [hA] at ht; simp at ht
      | coe A =>
        rw [hA] at ht hl
        rw [coe_add2, coe_add2, WithTop.coe_le_coe] at ht
        rw [WithTop.coe_le_coe] at hl; linarith
  -- chords
  have chord : ∀ i j, (T1 (γ i) (γ j) ∨ T2 (γ i) (γ j)) → γ j = γ (i + 1) := by
    intro i j hT
    obtain ⟨i', hi'⟩ : ∃ i', i % n0 = i' := ⟨_, rfl⟩
    obtain ⟨j', hj'⟩ : ∃ j', j % n0 = j' := ⟨_, rfl⟩
    have hi'lt : i' < n0 := hi' ▸ Nat.mod_lt _ hn0pos
    have hj'lt : j' < n0 := hj' ▸ Nat.mod_lt _ hn0pos
    rw [gmod i, gmod j, hi', hj'] at hT
    rw [gmod j, gsucc i, hi', hj']
    by_contra hne
    obtain ⟨m, hm⟩ : ∃ m, m = if j' ≤ i' then i' - j' + 1 else i' + n0 - j' + 1 := ⟨_, rfl⟩
    have hmpos : 0 < m := by
      by_cases hc : j' ≤ i'
      · rw [if_pos hc] at hm; omega
      · rw [if_neg hc] at hm; omega
    have hjm : γ (j' + (m - 1)) = γ i' := by
      by_cases hc : j' ≤ i'
      · rw [if_pos hc] at hm; rw [hm, show j' + (i' - j' + 1 - 1) = i' by omega]
      · rw [if_neg hc] at hm
        rw [hm, show j' + (i' + n0 - j' + 1 - 1) = i' + n0 by omega, per]
    have hmlt : m < n0 := by
      by_contra hge
      apply hne
      by_cases hc : j' ≤ i'
      · rw [if_pos hc] at hm
        rw [show j' = 0 by omega, show i' + 1 = 0 + n0 by omega, per]
      · rw [if_neg hc] at hm
        rw [show j' = i' + 1 by omega]
    apply hfm m hmlt
    refine ⟨hmpos, fun k => if k = m then γ j' else γ (j' + k), fun k hk => ?_, ?_⟩
    · simp only [if_neg (show k ≠ m by omega)]
      by_cases hk1 : k + 1 = m
      · simp only [if_pos hk1]
        rw [show k = m - 1 by omega, hjm]; exact hT
      · simp only [if_neg hk1, show j' + (k + 1) = j' + k + 1 by omega]; exact tight _
    · dsimp only; rw [if_pos rfl, if_neg (show (0 : ℕ) ≠ m by omega), Nat.add_zero]
  -- types
  let t : ℕ → Prop := fun k => T1 (γ k) (γ (k + 1))
  have tmod : ∀ k, t k ↔ t (k % n0) := by
    intro k; simp only [t]; rw [gsucc k, ← gmod k]
  have tper : ∀ k, t (k + n0) ↔ t k := by
    intro k; rw [tmod (k + n0), Nat.add_mod_right, ← tmod]
  have alt1 : ∀ k, t k → ¬ t (k + 1) := fun k h1' h2' => noTT1 _ _ _ h1' h2'
  have alt2 : ∀ k, ¬ t k → t (k + 1) := by
    intro k hk
    have a1 := (tight k).resolve_left hk
    rcases tight (k + 1) with h | h
    · exact h
    · exact (noTT2 _ _ _ a1 h).elim
  have teq : ∀ a b, γ a = γ b → (t a ↔ t b) := by
    intro a b he; rw [tmod a, tmod b, inj' a b he]
  let I1 := (Finset.range n0).filter t
  have memI : ∀ i, i ∈ I1 ↔ i < n0 ∧ t i := by
    intro i; simp [I1]
  have hI1ne : 0 < I1.card := by
    apply Finset.card_pos.2
    by_cases h0 : t 0
    · exact ⟨0, (memI 0).2 ⟨hn0pos, h0⟩⟩
    · exact ⟨1, (memI 1).2 ⟨by omega, alt2 0 h0⟩⟩
  -- first matching
  have hv1 : ∀ i ∈ I1, ∀ j ∈ I1, i ≠ j → γ (i + 1) ≠ γ (j + 1) := by
    intro i hi j hj hij he
    have := inj' _ _ he
    rw [mod_succ _ _ hn0pos, mod_succ _ _ hn0pos, Nat.mod_eq_of_lt ((memI i).1 hi).1,
      Nat.mod_eq_of_lt ((memI j).1 hj).1] at this
    have := ((memI i).1 hi).1; have := ((memI j).1 hj).1
    split_ifs at * <;> omega
  have huv1 : ∀ i ∈ I1, ∀ j ∈ I1, γ i ≠ γ (j + 1) := by
    intro i hi j hj he
    have := (teq _ _ he).1 ((memI i).1 hi).2
    exact alt1 j ((memI j).1 hj).2 this
  have M1 := ML hg1 (fun k => γ k) (fun k => γ (k + 1)) μ I1 x α1 hx1
    (fun i hi j hj hij he => hij (inj i j ((memI i).1 hi).1 ((memI j).1 hj).1 he)) hv1 huv1
    (fun i hi => ((memI i).1 hi).2.2)
    (fun i hi j hj hij => lt_of_le_of_ne (L1 _ _ (huv1 i hi j hj)) (fun he =>
      hv1 i hi j hj hij (chord i (j + 1) (Or.inl ⟨huv1 i hi j hj, he.symm⟩)).symm))
  -- second matching
  have pred_t : ∀ i ∈ I1, ¬ t (i + n0 - 1) := by
    intro i hi h
    have := alt1 _ h
    rw [show i + n0 - 1 + 1 = i + n0 by omega, tper] at this
    exact this ((memI i).1 hi).2
  have pred_T2 : ∀ i ∈ I1, T2 (γ (i + n0 - 1)) (γ i) := by
    intro i hi
    have := (tight (i + n0 - 1)).resolve_left (pred_t i hi)
    rwa [show i + n0 - 1 + 1 = i + n0 by omega, per] at this
  have hv2 : ∀ i ∈ I1, ∀ j ∈ I1, i ≠ j → γ (i + n0 - 1) ≠ γ (j + n0 - 1) := by
    intro i hi j hj hij he
    have := inj' _ _ he
    have hi' := ((memI i).1 hi).1; have hj' := ((memI j).1 hj).1
    have e : ∀ k, k < n0 → (k + n0 - 1) % n0 = if k = 0 then n0 - 1 else k - 1 := by
      intro k hk
      split_ifs with h0
      · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      · rw [show k + n0 - 1 = (k - 1) + n0 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e i hi', e j hj'] at this
    split_ifs at this <;> omega
  have huv2 : ∀ i ∈ I1, ∀ j ∈ I1, γ i ≠ γ (j + n0 - 1) := by
    intro i hi j hj he
    exact pred_t j hj ((teq _ _ he).1 ((memI i).1 hi).2)
  have hu0 : ∀ i ∈ I1, ∀ j ∈ I1, i ≠ j → γ i ≠ γ j :=
    fun i hi j hj hij he => hij (inj i j ((memI i).1 hi).1 ((memI j).1 hj).1 he)
  have M2 := ML hg2 (fun k => γ k) (fun k => γ (k + n0 - 1)) μ I1 x α2 hx2
    (fun i hi j hj hij he => hij (inj i j ((memI i).1 hi).1 ((memI j).1 hj).1 he)) hv2 huv2
    (fun i hi => (pred_T2 i hi).2)
    (fun i hi j hj hij => lt_of_le_of_ne (L2 _ _ (huv2 i hi j hj).symm) (fun he => by
      have := chord (j + n0 - 1) i (Or.inr ⟨(huv2 i hi j hj).symm, he.symm⟩)
      rw [show j + n0 - 1 + 1 = j + n0 by omega, per] at this
      exact hij (inj i j ((memI i).1 hi).1 ((memI j).1 hj).1 this)))
  -- the two bulk points agree
  have hbulk : bulk (fun k => γ k) (fun k => γ (k + 1)) x I1 =
      bulk (fun k => γ k) (fun k => γ (k + n0 - 1)) x I1 := by
    funext w
    simp only [bulk, Finset.sum_sub_distrib]
    congr 2
    simp only [I1, Finset.sum_filter]
    have hA : ∑ i ∈ Finset.range n0, (if t i then CharVec (γ (i + 1)) w else 0) =
        ∑ i ∈ Finset.range n0, (if ¬ t i then CharVec (γ i) w else 0) := by
      rw [← shift_sum (fun i => if ¬ t i then CharVec (γ i) w else 0) n0 (by
        have hγ : γ n0 = γ 0 := by simpa using per 0
        have ht : t n0 ↔ t 0 := by simpa using tper 0
        beta_reduce; simp only [hγ, ht])]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : t i
      · rw [if_pos h, if_pos (alt1 i h)]
      · rw [if_neg h, if_neg (not_not.2 (alt2 i h))]
    have hB : ∑ i ∈ Finset.range n0, (if t i then CharVec (γ (i + n0 - 1)) w else 0) =
        ∑ i ∈ Finset.range n0, (if ¬ t i then CharVec (γ i) w else 0) := by
      rw [← shift_sum (fun i => if t i then CharVec (γ (i + n0 - 1)) w else 0) n0 (by
        have hγ : γ (n0 + n0 - 1) = γ (0 + n0 - 1) := by
          rw [show n0 + n0 - 1 = (n0 - 1) + n0 by omega, per, Nat.zero_add]
        have ht : t n0 ↔ t 0 := by simpa using tper 0
        beta_reduce; simp only [hγ, ht])]
      apply Finset.sum_congr rfl
      intro i _
      rw [show i + 1 + n0 - 1 = i + n0 by omega, per]
      by_cases h : t i
      · rw [if_neg (alt1 i h), if_neg (not_not.2 h)]
      · rw [if_pos (alt2 i h), if_pos h]
    rw [hA, hB]
  rw [hbulk] at M1
  have hz := hmin _ _ ((card_img _ I1 hv2).trans (card_img _ I1 hu0).symm)
  rw [← bulk_eq _ _ I1 x hu0 hv2] at hz
  have := add_le_add M1 M2
  have h3 := hz.trans this
  rw [coe_add2, WithTop.coe_le_coe] at h3
  have : (0 : ℝ) < I1.card := by exact_mod_cast hI1ne
  nlinarith

end MIAux


open DiscreteConvex.MConvexFunctions MIGraph

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace MIAux

variable {W : Type*} [Fintype W] [DecidableEq W]

lemma untop_eq (A : WithTop ℝ) (h : A ≠ ⊤) : ((A.untopD 0 : ℝ) : WithTop ℝ) = A := by
  induction A using WithTop.recTopCoe with
  | top => exact absurd rfl h
  | coe a => simp

lemma L_neg (p : W → ℝ) (z : W → ℤ) : L (-p) z = - L p z := by
  simp [L, Finset.sum_neg_distrib]

lemma pf_sum (g1 g2 : (W → ℤ) → WithTop ℝ) (π : W → ℝ) (z : W → ℤ) :
    pf g1 (-π) z + pf g2 π z = g1 z + g2 z := by
  simp only [pf, L_neg]
  have : g1 z + ((-L π z : ℝ) : WithTop ℝ) + (g2 z + ((L π z : ℝ) : WithTop ℝ)) =
      g1 z + g2 z + ((-L π z + L π z : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_add]; ac_rfl
  rw [this, neg_add_cancel]; simp

theorem mconv_intersection {g1 g2 : (W → ℤ) → WithTop ℝ} (hg1 : MExchangeAxiom g1)
    (hg2 : MExchangeAxiom g2) (x : W → ℤ) (hx1 : g1 x ≠ ⊤) (hx2 : g2 x ≠ ⊤)
    (hmin : ∀ Y Z : Finset W, Y.card = Z.card → g1 x + g2 x ≤
      g1 (fun w => x w + ind Y w - ind Z w) + g2 (fun w => x w + ind Y w - ind Z w)) :
    ∃ π : W → ℝ, (∀ z, pf g1 (-π) x ≤ pf g1 (-π) z) ∧ (∀ z, pf g2 π x ≤ pf g2 π z) := by
  classical
  obtain ⟨α1, hα1⟩ := WithTop.ne_top_iff_exists.1 hx1
  obtain ⟨α2, hα2⟩ := WithTop.ne_top_iff_exists.1 hx2
  replace hα1 := hα1.symm
  replace hα2 := hα2.symm
  let E : W → W → Bool → Prop := fun a b l =>
    if l then a ≠ b ∧ g1 (xm x a b) ≠ ⊤ else a ≠ b ∧ g2 (xm x b a) ≠ ⊤
  let c : W → W → Bool → ℝ := fun a b l =>
    if l then (g1 (xm x a b)).untopD 0 - α1 else (g2 (xm x b a)).untopD 0 - α2
  have E1 : ∀ a b, E a b true → a ≠ b ∧ g1 (xm x a b) = ((α1 + c a b true : ℝ) : WithTop ℝ) := by
    intro a b h
    simp only [E, c, if_true] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [show α1 + ((g1 (xm x a b)).untopD 0 - α1) = (g1 (xm x a b)).untopD 0 by ring,
      untop_eq _ h.2]
  have E2 : ∀ a b, E a b false → a ≠ b ∧ g2 (xm x b a) = ((α2 + c a b false : ℝ) : WithTop ℝ) := by
    intro a b h
    simp only [E, c, Bool.false_eq_true, if_false] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [show α2 + ((g2 (xm x b a)).untopD 0 - α2) = (g2 (xm x b a)).untopD 0 by ring,
      untop_eq _ h.2]
  have E1' : ∀ a b, a ≠ b → g1 (xm x a b) ≠ ⊤ → E a b true := by
    intro a b h1 h2; simp only [E, if_true]; exact ⟨h1, h2⟩
  have E2' : ∀ a b, a ≠ b → g2 (xm x b a) ≠ ⊤ → E a b false := by
    intro a b h1 h2; simp only [E, Bool.false_eq_true, if_false]; exact ⟨h1, h2⟩
  have hmin' : ∀ π : W → ℝ, ∀ Y Z : Finset W, Y.card = Z.card →
      (((α1 + L (-π) x) + (α2 + L π x) : ℝ) : WithTop ℝ) ≤
      pf g1 (-π) (fun w => x w + ind Y w - ind Z w) + pf g2 π (fun w => x w + ind Y w - ind Z w) := by
    intro π Y Z hYZ
    rw [pf_sum, L_neg, show α1 + -L π x + (α2 + L π x) = α1 + α2 by ring, ← coe_add2, ← hα1, ← hα2]
    exact hmin Y Z hYZ
  -- no negative closed walk
  have noneg : ∀ m δ τ, IsWalk E δ τ m → δ m = δ 0 → 0 ≤ wt c δ τ m := by
    by_contra hneg
    push Not at hneg
    obtain ⟨μ, hμ, hall, m0, δ0, τ0, hm0, hw0, hc0, hwt0⟩ := min_mean (E := E) (c := c) hneg
    let c' : W → W → Bool → ℝ := fun a b l => c a b l - μ
    have wt' : ∀ m δ τ, wt c' δ τ m = wt c δ τ m - m * μ := by
      intro m δ τ
      simp [wt, c', Finset.sum_sub_distrib]
    obtain ⟨π, hπ⟩ := potential (E := E) (c := c') (fun m δ τ hw hc => by
      rw [wt']; linarith [hall m δ τ hw hc])
    apply core2 (pf_exch g1 hg1 (-π)) (pf_exch g2 hg2 π) x (α1 + L (-π) x) (α2 + L π x) μ
      (by rw [pf, hα1, coe_add2]) (by rw [pf, hα2, coe_add2]) hμ (hmin' π)
    · intro a b hab
      by_cases ht : g1 (xm x a b) = ⊤
      · simp [pf, ht]
      obtain ⟨_, he⟩ := E1 a b (E1' a b hab ht)
      have hp := hπ a b true (E1' a b hab ht)
      simp only [c'] at hp
      rw [pf, he, coe_add2, WithTop.coe_le_coe, L_xm]
      simp only [Pi.neg_apply]; linarith
    · intro a b hab
      by_cases ht : g2 (xm x b a) = ⊤
      · simp [pf, ht]
      obtain ⟨_, he⟩ := E2 a b (E2' a b hab ht)
      have hp := hπ a b false (E2' a b hab ht)
      simp only [c'] at hp
      rw [pf, he, coe_add2, WithTop.coe_le_coe, L_xm]
      linarith
    · -- the minimum mean walk is tight
      refine ⟨m0, δ0, hm0, ?_, hc0⟩
      have hr : ∀ k ∈ Finset.range m0,
          0 ≤ c (δ0 k) (δ0 (k + 1)) (τ0 k) - μ + π (δ0 k) - π (δ0 (k + 1)) := by
        intro k hk
        have := hπ _ _ _ (hw0 k (Finset.mem_range.1 hk)); simp only [c'] at this; linarith
      have hsum : ∑ k ∈ Finset.range m0,
          (c (δ0 k) (δ0 (k + 1)) (τ0 k) - μ + π (δ0 k) - π (δ0 (k + 1))) = 0 := by
        have h1 : ∑ k ∈ Finset.range m0,
            (c (δ0 k) (δ0 (k + 1)) (τ0 k) - μ + π (δ0 k) - π (δ0 (k + 1))) =
            wt c δ0 τ0 m0 - m0 * μ + ∑ k ∈ Finset.range m0, (π (δ0 k) - π (δ0 (k + 1))) := by
          simp only [wt, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          ring
        rw [h1, Finset.sum_range_sub' (fun k => π (δ0 k)), hc0, hwt0]; ring
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hr).1 hsum
      intro k hk
      have hzk := hz k (Finset.mem_range.2 hk)
      have hwk := hw0 k hk
      cases hτ : τ0 k
      · rw [hτ] at hzk hwk
        obtain ⟨hne, he⟩ := E2 _ _ hwk
        right
        refine ⟨hne, ?_⟩
        rw [pf, he, coe_add2, L_xm]
        congr 1; linarith
      · rw [hτ] at hzk hwk
        obtain ⟨hne, he⟩ := E1 _ _ hwk
        left
        refine ⟨hne, ?_⟩
        rw [pf, he, coe_add2, L_xm]
        congr 1; simp only [Pi.neg_apply]; linarith
  obtain ⟨π, hπ⟩ := potential (E := E) (c := c) noneg
  refine ⟨π, LG (pf_exch g1 hg1 (-π)) x ((pf_ne_top _ _ _).2 hx1) ?_,
    LG (pf_exch g2 hg2 π) x ((pf_ne_top _ _ _).2 hx2) ?_⟩
  · intro a b
    by_cases hab : a = b
    · rw [hab, xm_self]
    by_cases ht : g1 (xm x a b) = ⊤
    · simp [pf, ht]
    obtain ⟨_, he⟩ := E1 a b (E1' a b hab ht)
    have hp := hπ a b true (E1' a b hab ht)
    rw [pf, pf, he, hα1, coe_add2, coe_add2, WithTop.coe_le_coe, L_xm]
    simp only [Pi.neg_apply]; linarith
  · intro a b
    by_cases hab : a = b
    · rw [hab, xm_self]
    by_cases ht : g2 (xm x a b) = ⊤
    · simp [pf, ht]
    obtain ⟨_, he⟩ := E2 b a (E2' b a (Ne.symm hab) ht)
    have hp := hπ b a false (E2' b a (Ne.symm hab) ht)
    rw [pf, pf, he, hα2, coe_add2, coe_add2, WithTop.coe_le_coe, L_xm]
    linarith

end MIAux


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace MIAux

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma ind_eq (Y : Finset V) : DiscreteConvex.ConjugacyDualityB.IndicatorVec Y = ind Y := by
  funext w
  simp only [DiscreteConvex.ConjugacyDualityB.IndicatorVec, ind]

lemma bridge (f : (V → ℤ) → WithTop ℝ) (h : DiscreteConvex.ConjugacyDualityB.MExchangeAxiom f) :
    DiscreteConvex.MConvexFunctions.MExchangeAxiom f := by
  intro x hx y hy u hu
  obtain ⟨v, hv, hineq⟩ := h x hx y hy u (by
    simpa [DiscreteConvex.ConjugacyDualityB.SuppPos, DiscreteConvex.MConvexFunctions.SuppPos] using hu)
  refine ⟨v, by
    simpa [DiscreteConvex.ConjugacyDualityB.SuppNeg, DiscreteConvex.MConvexFunctions.SuppNeg] using hv, ?_⟩
  have e1 : ∀ a : V, DiscreteConvex.ConjugacyDualityB.IndicatorVec {a} =
      DiscreteConvex.MConvexFunctions.CharVec a := by
    intro a; funext w
    simp only [DiscreteConvex.ConjugacyDualityB.IndicatorVec, DiscreteConvex.MConvexFunctions.CharVec]
    split_ifs <;> simp_all
  simpa only [e1] using hineq

end MIAux

open MIAux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : DiscreteConvex.ConjugacyDualityB.M2Convex f) (x : V → ℤ)
    (hx : x ∈ DiscreteConvex.ConjugacyDualityB.DomZ f) :
    (∀ y : V → ℤ, f x ≤ f y) ↔
      (∀ Y Z : Finset V, Y.card = Z.card →
        f x ≤ f (fun v => x v + DiscreteConvex.ConjugacyDualityB.IndicatorVec Y v -
          DiscreteConvex.ConjugacyDualityB.IndicatorVec Z v)) := by
  constructor
  · intro h Y Z _; exact h _
  · intro hloc y
    obtain ⟨f1, f2, h1, h2, rfl⟩ := hf
    have hx' : f1 x + f2 x ≠ ⊤ := hx
    obtain ⟨hx1, hx2⟩ := WithTop.add_ne_top.1 hx'
    obtain ⟨π, g1, g2⟩ := mconv_intersection (bridge f1 h1) (bridge f2 h2) x hx1 hx2 (by
      intro Y Z hc
      have := hloc Y Z hc
      simpa only [ind_eq] using this)
    have := add_le_add (g1 y) (g2 y)
    rwa [pf_sum, pf_sum] at this

