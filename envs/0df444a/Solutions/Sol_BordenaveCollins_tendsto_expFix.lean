-- Prove2me | solution 1 for BordenaveCollins.tendsto_expFix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:20:41.220795+00:00
-- url     : https://prove2.me/submissions/27ec2b7d-adb9-48ae-aa0c-5fe28fdd5865

import Mathlib
import Definitions.Def_BordenaveCollins

section
/-!
# Strong convergence of random permutations and perfect matchings: auxiliary definitions

Definitions used only inside the proof of `DerandSq.theorem_2_14` (reduced words, colourings of the
closed path of a word, the model operators and their spectral functional, the bridge from
noncommutative polynomials to the group algebra).
-/

open Finset

noncomputable section

namespace BordenaveCollins

/-! ## The group and its letters -/

/-- The inverse letter. -/
def bar {r s : ℕ} : Lt r s → Lt r s
  | Sum.inl (i, b) => Sum.inl (i, !b)
  | Sum.inr j => Sum.inr j

/-- A reduced word: no letter is followed by its inverse. -/
def Red {r s : ℕ} (u : List (Lt r s)) : Prop := u.IsChain (fun a b => b ≠ bar a)

/-- `u` is cyclically reduced: no letter is followed (cyclically) by its inverse. (A one-letter
word `[m_j]` is not cyclically reduced in this sense.) -/
def CycRed {r s : ℕ} (u : List (Lt r s)) : Prop :=
  ∀ t : Fin u.length,
    u.get ⟨(t.val + 1) % u.length, Nat.mod_lt _ (by have := t.2; omega)⟩ ≠ bar (u.get t)

/-- The number of periods of a cyclic word: divisors `ℓ` of the length with `u[t + ℓ] = u[t]`
cyclically (`ℓ = length` always counts). -/
def per {r s : ℕ} (u : List (Lt r s)) : ℕ :=
  ((Nat.divisors u.length).filter fun ℓ => ∀ t : Fin u.length,
    u.get ⟨(t.val + ℓ) % u.length, Nat.mod_lt _ (by have := t.2; omega)⟩ = u.get t).card

/-! ## The random model -/

/-- The permutation of a letter. -/
def letterPerm {r s N : ℕ} (ω : Om r s N) : Lt r s → Equiv.Perm (Fin N)
  | Sum.inl (i, true) => ω.1 i
  | Sum.inl (i, false) => (ω.1 i)⁻¹
  | Sum.inr j => (ω.2 j).1

/-- The permutation of a word (product in the order the letters appear). -/
def wordPerm {r s N : ℕ} (ω : Om r s N) (u : List (Lt r s)) : Equiv.Perm (Fin N) :=
  (u.map (letterPerm ω)).prod

/-- `E[fix(wordPerm ω u)]` over a uniform sample. -/
def expFixW (r s N : ℕ) (u : List (Lt r s)) : ℝ :=
  (∑ ω : Om r s N, (fixCount (wordPerm ω u) : ℝ)) / (Fintype.card (Om r s N) : ℝ)

/-! ## Colourings of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPerm ω (u.drop t) y`). -/

section Colour

variable {r s : ℕ} (u : List (Lt r s))

/-- A finite set of pairs is the graph of a partial injection. -/
def PInj {α : Type*} (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

/-- A finite set of unordered pairs is a partial matching: no loops, pairwise disjoint. -/
def PMat {α : Type*} (E : Finset (Sym2 α)) : Prop :=
  (∀ p ∈ E, ¬ p.IsDiag) ∧ ∀ p ∈ E, ∀ q ∈ E, (∃ a, a ∈ p ∧ a ∈ q) → p = q

/-- The directed edges `(a, b)` with `σ_i a = b` forced by the steps labelled `u_i^{±1}`. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) : Finset (α × α) :=
  ((univ.filter fun t : Fin u.length => u.get t = Sum.inl (i, true)).image
      fun t => (x t.succ, x t.castSucc)) ∪
    ((univ.filter fun t : Fin u.length => u.get t = Sum.inl (i, false)).image
      fun t => (x t.castSucc, x t.succ))

/-- The unordered pairs forced to be edges of the matching `M_j`. -/
def Ms {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (j : Fin s) : Finset (Sym2 α) :=
  (univ.filter fun t : Fin u.length => u.get t = Sum.inr j).image
    fun t => s(x t.castSucc, x t.succ)

/-- A closed path whose edge sets are partial injections and partial matchings. -/
def Good {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) : Prop :=
  (∀ i, PInj (Es u x i)) ∧ (∀ j, PMat (Ms u x j)) ∧ x 0 = x (Fin.last _)

/-- The first position where `x` takes the value `x t`. -/
def canon {n : ℕ} {α : Type*} [DecidableEq α] (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

/-- The number of values of a path. -/
def nv {n : ℕ} {α : Type*} [DecidableEq α] (x : Fin n → α) : ℕ := (univ.image x).card

/-- Canonical good colourings of the closed path of `u`. -/
def CG : Finset (Fin (u.length + 1) → Fin (u.length + 1)) := by
  classical exact (univ.filter fun c => canon c = c).filter (Good u)

/-- The number of edges of a colouring. -/
def Ecount (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℕ :=
  ∑ i, (Es u c i).card + ∑ j, (Ms u c j).card

/-- The weight of a colouring: the expected number of injective labellings realised. -/
def wt (N : ℕ) (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℝ :=
  (N.descFactorial (nv c) : ℝ) /
    ((∏ i, (N.descFactorial (Es u c i).card : ℝ)) *
      ∏ j, ∏ l ∈ range (Ms u c j).card, ((N : ℝ) - 2 * l - 1))

end Colour

/-! ## Matrix coefficients -/

end BordenaveCollins

end

/-! ## Definitions of the bridge and crude bounds -/

open Finset Filter Topology Polynomial
open scoped Classical

end

section
/-!
# Part F1: normal forms in `F_r * Γ_s` (van der Waerden's trick)
-/

open Finset

noncomputable section

namespace BordenaveCollins.PartF1

open BordenaveCollins

variable {r s : ℕ}

/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/

theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a
theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a
theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a
theorem g_inv_one : (1 : G r s)⁻¹ = 1 := inv_one
theorem g_mul_inv_rev (a b : G r s) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm
theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/

@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/

@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

theorem wprod_singleton (a : Lt r s) : wprod [a] = genL a := by simp

/-! ## The push action on reduced words -/

/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem push_of_red_cons {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) :
    push a t = a :: t := by
  cases t with
  | nil => rfl
  | cons b t => exact push_cons_ne _ _ _ (red_cons_cons.1 h).1

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

theorem red_nf (g : G r s) : Red (nf g) := (hom r s g ⟨[], red_nil⟩).2

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem hom_wprod_nil (u : List (Lt r s)) (hu : Red u) :
    hom r s (wprod u) ⟨[], red_nil⟩ = ⟨u, hu⟩ := by
  induction u with
  | nil => simp
  | cons a t ih =>
    apply Subtype.ext
    rw [wprod_cons, hom_genL_mul, ih (Red.tail' hu)]
    exact push_of_red_cons hu

theorem nf_wprod (u : List (Lt r s)) (hu : Red u) : nf (wprod u) = u :=
  congrArg Subtype.val (hom_wprod_nil u hu)

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem nf_injective : Function.Injective (nf : G r s → List (Lt r s)) := by
  intro g h e
  rw [← wprod_nf g, e, wprod_nf]

theorem nf_eq_nil_iff (g : G r s) : nf g = [] ↔ g = 1 :=
  ⟨fun h => nf_injective (h.trans nf_one.symm), fun h => h ▸ nf_one⟩

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

theorem len_wprod_le (u : List (Lt r s)) : len (wprod u) ≤ u.length := len_le_of_wprod rfl

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

theorem nf_exists (r s : ℕ) : ∃ nf : G r s → List (Lt r s),
    (∀ g, Red (nf g)) ∧ (∀ g, wprod (nf g) = g) ∧ (∀ u, Red u → nf (wprod u) = u) ∧
      ∀ g, len g = (nf g).length :=
  ⟨nf, red_nf, wprod_nf, nf_wprod, len_eq_length_nf⟩

theorem act_genL {N : ℕ} (ω : Om r s N) (a : Lt r s) : act ω (genL a) = letterPerm ω a := by
  rcases a with ⟨i, b⟩ | j
  · have h1 : act ω (genL (Sum.inl (i, true))) = ω.1 i := by simp [act, genL]
    cases b
    · show act ω (genL (Sum.inl (i, true)))⁻¹ = (ω.1 i)⁻¹
      rw [g_map_inv, h1]
    · exact h1
  · simp only [act, genL, letterPerm, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    show (ω.2 j).1 ^ (1 : ZMod 2).val = _
    simp [ZMod.val_one]

theorem act_wprod {N : ℕ} (ω : Om r s N) (u : List (Lt r s)) :
    act ω (wprod u) = wordPerm ω u := by
  induction u with
  | nil => simp [wordPerm]
  | cons a t ih =>
    rw [wprod_cons, map_mul, ih, act_genL]
    simp [wordPerm]

theorem getElem_congr_idx (u : List (Lt r s)) {i j : ℕ} (hi : i < u.length) (hj : j < u.length)
    (h : i = j) : u[i] = u[j] := by subst h; rfl

/-- A reduced nonempty word whose first letter is not the inverse of its last letter is
cyclically reduced. -/
theorem cycRed_of_red (u : List (Lt r s)) (hu : Red u) (hne : u ≠ [])
    (h : u.head hne ≠ bar (u.getLast hne)) : CycRed u := by
  intro t
  have hpos : 0 < u.length := List.length_pos_iff.2 hne
  simp only [List.get_eq_getElem]
  by_cases ht : t.val + 1 < u.length
  · have := (List.isChain_iff_getElem.1 hu) t.val ht
    rw [getElem_congr_idx u (Nat.mod_lt _ hpos) ht (Nat.mod_eq_of_lt ht)]
    exact this
  · have ht' : t.val = u.length - 1 := by have := t.2; omega
    have h0 : (t.val + 1) % u.length = 0 := by
      rw [ht', Nat.sub_add_cancel hpos, Nat.mod_self]
    rw [getElem_congr_idx u (Nat.mod_lt _ hpos) hpos h0,
      getElem_congr_idx u t.2 (by omega) ht']
    rw [List.head_eq_getElem, List.getLast_eq_getElem] at h
    exact h

theorem exists_cyc_rep (g : G r s) (hg : g ≠ 1) :
    ∃ (a : G r s) (u : List (Lt r s)), u ≠ [] ∧ g = a * wprod u * a⁻¹ ∧
      (CycRed u ∨ ∃ j : Fin s, u = [Sum.inr j]) := by
  induction hn : len g using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    have hne : nf g ≠ [] := fun h => hg ((nf_eq_nil_iff g).1 h)
    by_cases hc : (nf g).head hne ≠ bar ((nf g).getLast hne)
    · exact ⟨1, nf g, hne, by rw [wprod_nf, g_inv_one, one_mul, mul_one], Or.inl (cycRed_of_red _ (red_nf g) hne hc)⟩
    · rw [not_not] at hc
      obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
      cases t with
      | nil =>
        rcases a with ⟨i, b⟩ | j
        · simp [hat, bar] at hc
        · exact ⟨1, nf g, hne, by rw [wprod_nf, g_inv_one, one_mul, mul_one], Or.inr ⟨j, hat⟩⟩
      | cons b t' =>
        have hne' : (b :: t') ≠ [] := by simp
        have hsplit := List.dropLast_append_getLast hne'
        set m := (b :: t').dropLast with hm
        set c := (b :: t').getLast hne' with hcdef
        have hac : a = bar c := by
          simp only [hat, List.head_cons, List.getLast_cons hne'] at hc
          exact hc
        have hgm : g = genL a * wprod m * (genL a)⁻¹ := by
          rw [← wprod_nf g, hat, ← hsplit, wprod_cons, wprod_append, wprod_singleton, hac,
            genL_bar c, g_inv_inv, mul_assoc]
        have hm1 : wprod m ≠ 1 := by
          intro h1
          apply hg
          rw [hgm, h1, mul_one, g_mul_inv_cancel]
        have hlen : len (wprod m) < n := by
          have h1 := len_wprod_le m
          have h2 : (nf g).length = m.length + 2 := by
            rw [hat, ← hsplit]; simp
          rw [← hn, len_eq_length_nf g]
          omega
        obtain ⟨a', u, hu, he, hcu⟩ := ih _ hlen (wprod m) hm1 rfl
        refine ⟨genL a * a', u, hu, ?_, hcu⟩
        rw [hgm, he, g_mul_inv_rev]
        simp only [mul_assoc]

end BordenaveCollins.PartF1
end
end

section
/-!
# The statements proved in Part F1, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

/-- Reduced words are a normal form, and `len` is the length of the reduced word. -/
theorem nf_exists (r s : ℕ) : ∃ nf : G r s → List (Lt r s),
    (∀ g, Red (nf g)) ∧ (∀ g, wprod (nf g) = g) ∧ (∀ u, Red u → nf (wprod u) = u) ∧
      ∀ g, len g = (nf g).length :=
  PartF1.nf_exists r s

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ :=
  PartF1.genL_bar a

/-- Every nontrivial element is conjugate to a cyclically reduced word or to a letter `m_j`. -/
theorem exists_cyc_rep (g : G r s) (hg : g ≠ 1) :
    ∃ (a : G r s) (u : List (Lt r s)), u ≠ [] ∧ g = a * wprod u * a⁻¹ ∧
      (CycRed u ∨ ∃ j : Fin s, u = [Sum.inr j]) :=
  PartF1.exists_cyc_rep g hg

end BordenaveCollins

end
end

section
/-!
# Part K: colourings of cyclically reduced words

`nv_le_Ecount` (no leaves, so vertices ≤ edges) and `card_eq_per` (vertices = edges exactly for the
periodic colourings `t ↦ t mod ℓ`).
-/

open Finset
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartK

section Gen

variable {r s : ℕ} {α : Type*} [DecidableEq α]

/-- Labelled edges: directed for permutation letters, unordered for matching letters. -/
abbrev Edge (r s : ℕ) (α : Type*) := (Fin r × (α × α)) ⊕ (Fin s × Sym2 α)

/-- The labelled edge of a step from `a` to `b` with letter `l`. -/
def ed : Lt r s → α → α → Edge r s α
  | Sum.inl (i, true), a, b => Sum.inl (i, (b, a))
  | Sum.inl (i, false), a, b => Sum.inl (i, (a, b))
  | Sum.inr j, a, b => Sum.inr (j, s(a, b))

/-- The labelled edge of step `t`. -/
def ee (a : ℕ → Lt r s) (x : ℕ → α) (t : ℕ) : Edge r s α := ed (a t) (x t) (x (t + 1))

/-- The vertices visited at times `≤ k`. -/
def UU (x : ℕ → α) (k : ℕ) : Finset α := (range (k + 1)).image x

/-- The labelled edges of steps `< k`. -/
def EE (a : ℕ → Lt r s) (x : ℕ → α) (k : ℕ) : Finset (Edge r s α) :=
  (range k).image (ee a x)

/-- Step `k` is a closing step. -/
def closing (a : ℕ → Lt r s) (x : ℕ → α) (k : ℕ) : Prop :=
  x (k + 1) ∈ UU x k ∧ ee a x k ∉ EE a x k

lemma mem_UU {x : ℕ → α} {k j : ℕ} (h : j ≤ k) : x j ∈ UU x k :=
  mem_image_of_mem _ (mem_range.2 (by omega))

lemma UU_succ (x : ℕ → α) (k : ℕ) : UU x (k + 1) = insert (x (k + 1)) (UU x k) := by
  simp [UU, range_add_one, image_insert]

lemma EE_succ (a : ℕ → Lt r s) (x : ℕ → α) (k : ℕ) :
    EE a x (k + 1) = insert (ee a x k) (EE a x k) := by
  simp [EE, range_add_one, image_insert]

omit [DecidableEq α] in
lemma ed_eq {l1 l2 : Lt r s} {a b a' b' : α} (h : ed l1 a b = ed l2 a' b') :
    (l2 = l1 ∧ a' = a ∧ b' = b) ∨ (l2 = bar l1 ∧ a' = b ∧ b' = a) := by
  rcases l1 with ⟨i, _ | _⟩ | j <;> rcases l2 with ⟨i', _ | _⟩ | j' <;>
    simp only [ed, bar, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq, Sym2.eq_iff,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, and_false,
      false_and, or_false, false_or] at h ⊢ <;>
    tauto

omit [DecidableEq α] in
lemma ee_eq {a : ℕ → Lt r s} {x : ℕ → α} {s' t : ℕ} (h : ee a x s' = ee a x t) :
    (a t = a s' ∧ x t = x s' ∧ x (t + 1) = x (s' + 1)) ∨
      (a t = bar (a s') ∧ x t = x (s' + 1) ∧ x (t + 1) = x s') :=
  ed_eq h

omit [DecidableEq α] in
lemma bar_bar (l : Lt r s) : bar (bar l) = l := by
  rcases l with ⟨i, _ | _⟩ | j <;> rfl

lemma count (a : ℕ → Lt r s) (x : ℕ → α) :
    ∀ k, (UU x k).card + ((range k).filter (closing a x)).card = (EE a x k).card + 1
  | 0 => by simp [UU, EE]
  | k + 1 => by
      have ih := count a x k
      rw [UU_succ, EE_succ, range_add_one, filter_insert]
      have hk : k ∉ range k := by simp
      by_cases hx : x (k + 1) ∈ UU x k
      · by_cases he : ee a x k ∈ EE a x k
        · have hc : ¬ closing a x k := fun h => h.2 he
          rw [if_neg hc, insert_eq_of_mem hx, insert_eq_of_mem he]; exact ih
        · have hc : closing a x k := ⟨hx, he⟩
          rw [if_pos hc, insert_eq_of_mem hx, card_insert_of_notMem he,
            card_insert_of_notMem (fun h => hk (mem_filter.1 h).1)]
          omega
      · have he : ee a x k ∉ EE a x k := by
          intro h
          obtain ⟨s', hs, hse⟩ := mem_image.1 h
          have hs := mem_range.1 hs
          rcases ee_eq hse with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
          · exact hx (h3 ▸ mem_UU (by omega))
          · exact hx (h3 ▸ mem_UU (by omega))
        have hc : ¬ closing a x k := fun h => hx h.1
        rw [if_neg hc, card_insert_of_notMem hx, card_insert_of_notMem he]
        omega

variable {L : ℕ} {a : ℕ → Lt r s} {x : ℕ → α}

lemma step0 (h : ¬ closing a x 0) : x 1 ∉ UU x 0 := by
  intro hx
  exact h ⟨hx, by simp [EE]⟩

lemma step_new (hcr : ∀ t, t + 1 < L → a (t + 1) ≠ bar (a t))
    {t : ℕ} (ht1 : 1 ≤ t) (htL : t < L) (hnew : x t ∉ UU x (t - 1)) (hnc : ¬ closing a x t) :
    x (t + 1) ∉ UU x t := by
  intro hin
  have he : ee a x t ∈ EE a x t := by
    by_contra h; exact hnc ⟨hin, h⟩
  obtain ⟨s', hs, hse⟩ := mem_image.1 he
  have hs := mem_range.1 hs
  rcases ee_eq hse with ⟨-, h2, -⟩ | ⟨h1, h2, -⟩
  · exact hnew (h2 ▸ mem_UU (by omega))
  · by_cases hst : s' + 1 ≤ t - 1
    · exact hnew (h2 ▸ mem_UU hst)
    · have : s' = t - 1 := by omega
      subst this
      exact hcr (t - 1) (by omega) (by rw [show t - 1 + 1 = t by omega]; exact h1)

lemma chain (hcr : ∀ t, t + 1 < L → a (t + 1) ≠ bar (a t))
    {t0 : ℕ} (h1 : 1 ≤ t0) (hnew : x t0 ∉ UU x (t0 - 1)) :
    ∀ t1, t0 ≤ t1 → t1 ≤ L → (∀ j, t0 ≤ j → j < t1 → ¬ closing a x j) →
      x t1 ∉ UU x (t1 - 1) := by
  intro t1 h01
  induction t1, h01 using Nat.le_induction with
  | base => intro _ _; exact hnew
  | succ t1 h0t ih =>
    intro hL hnc
    have := step_new hcr (by omega) (by omega) (ih (by omega)
      (fun j hj hj' => hnc j hj (by omega))) (hnc t1 h0t (by omega))
    simpa using this

omit [DecidableEq α] in
lemma hcr_lin (hcr : ∀ t < L, a ((t + 1) % L) ≠ bar (a t)) :
    ∀ t, t + 1 < L → a (t + 1) ≠ bar (a t) := by
  intro t ht
  have := hcr t (by omega)
  rwa [Nat.mod_eq_of_lt ht] at this

theorem gen_le (hL : 1 ≤ L) (hcr : ∀ t < L, a ((t + 1) % L) ≠ bar (a t)) (hcl : x L = x 0) :
    (UU x L).card ≤ (EE a x L).card := by
  have hc := count a x L
  suffices h : ((range L).filter (closing a x)).card ≠ 0 by omega
  intro h0
  rw [card_eq_zero, filter_eq_empty_iff] at h0
  have hnc : ∀ j, j < L → ¬ closing a x j := fun j hj => h0 (mem_range.2 hj)
  have hx1 := step0 (hnc 0 (by omega))
  have := chain (hcr_lin hcr) (le_refl 1) hx1 L hL le_rfl (fun j _ hj => hnc j hj)
  exact this (hcl ▸ mem_UU (Nat.zero_le _))

lemma mod_succ_inj {M j jj : ℕ} (hj : j < M) (hjj : jj < M) (h : (j + 1) % M = (jj + 1) % M) :
    j = jj := by
  rcases Nat.lt_or_ge (j + 1) M with h1 | h1 <;> rcases Nat.lt_or_ge (jj + 1) M with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, show jj + 1 = M by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show j + 1 = M by omega, Nat.mod_self] at h; omega
  · omega

theorem gen_struct (hL : 1 ≤ L) (hcr : ∀ t < L, a ((t + 1) % L) ≠ bar (a t)) (hcl : x L = x 0)
    (hVE : (UU x L).card = (EE a x L).card) :
    ∃ M, 1 ≤ M ∧ M ∣ L ∧ (∀ t < L, a t = a (t % M)) ∧
      ∀ u ≤ L, ∀ v ≤ L, (x u = x v ↔ u % M = v % M) := by
  have hcl' := hcr_lin hcr
  have hc := count a x L
  obtain ⟨ts, hts⟩ := card_eq_one.1 (show ((range L).filter (closing a x)).card = 1 by omega)
  have htsL : ts < L := mem_range.1 (mem_filter.1 (hts ▸ mem_singleton_self ts)).1
  have hcts : closing a x ts := (mem_filter.1 (hts ▸ mem_singleton_self ts)).2
  have huniq : ∀ j < L, closing a x j → j = ts := fun j hj hcj =>
    mem_singleton.1 (hts ▸ mem_filter.2 ⟨mem_range.2 hj, hcj⟩)
  set M := ts + 1 with hMdef
  have hnewj : ∀ j, 1 ≤ j → j < M → x j ∉ UU x (j - 1) := by
    intro j hj1 hjM
    have h0 : ¬ closing a x 0 := fun h => by have := huniq 0 (by omega) h; omega
    exact chain hcl' (le_refl 1) (step0 h0) j hj1 (by omega)
      (fun i hi hij hcl2 => by have := huniq i (by omega) hcl2; omega)
  have hD : ∀ i j, i < M → j < M → x i = x j → i = j := by
    intro i j hi hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hnewj j (by omega) hj (hij ▸ mem_UU (by omega))
    · exact hnewj i (by omega) hi (hij ▸ mem_UU (by omega))
  have hafter : ∀ t, M ≤ t → t < L → x (t + 1) ∈ UU x t := by
    intro t ht1 ht2
    by_contra hn
    exact chain hcl' (show 1 ≤ t + 1 by omega) (by simpa using hn) L (by omega) le_rfl
      (fun j hj hj2 hcj => by have := huniq j hj2 hcj; omega)
      (show x L ∈ UU x (L - 1) by rw [hcl]; exact mem_UU (Nat.zero_le _))
  have hrep : ∀ t, M ≤ t → t < L → ee a x t ∈ EE a x t := by
    intro t ht1 ht2
    by_contra h
    have := huniq t ht2 ⟨hafter t ht1 ht2, h⟩
    omega
  have hback : ∀ t, t < L → ∃ j < M, ee a x t = ee a x j := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro htL
      by_cases htM : t < M
      · exact ⟨t, htM, rfl⟩
      · obtain ⟨s', hs, hse⟩ := mem_image.1 (hrep t (by omega) htL)
        have hs := mem_range.1 hs
        obtain ⟨j, hj, hje⟩ := ih s' hs (by omega)
        exact ⟨j, hj, hse.symm.trans hje⟩
  have hM0 : x M = x 0 := by
    obtain ⟨s', hs, hse⟩ := mem_image.1 hcts.1
    have hs := mem_range.1 hs
    by_cases hs0 : s' = 0
    · subst hs0; exact hse.symm
    exfalso
    by_cases hML : M = L
    · have : x s' = x 0 := by rw [hse, show ts + 1 = L from hML, hcl]
      exact hs0 (hD s' 0 (by omega) (by omega) this)
    · obtain ⟨j, hj, hje⟩ := hback (L - 1) (by omega)
      have hL1 : L - 1 + 1 = L := by omega
      rcases ee_eq hje.symm with ⟨-, -, h3⟩ | ⟨h1, -, h3⟩
      · rw [hL1, hcl] at h3
        by_cases hjM : j + 1 < M
        · have := hD 0 (j + 1) (by omega) hjM h3; omega
        · have : j + 1 = M := by omega
          rw [this, hMdef, ← hse] at h3
          exact hs0 (hD 0 s' (by omega) (by omega) h3).symm
      · rw [hL1, hcl] at h3
        have hj0 : j = 0 := (hD 0 j (by omega) hj h3).symm
        subst hj0
        apply hcr (L - 1) (by omega)
        rw [hL1, Nat.mod_self, h1, bar_bar]
  have hxM : ∀ v ≤ M, x v = x (v % M) := by
    intro v hv
    rcases Nat.lt_or_ge v M with h | h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show v = M by omega, Nat.mod_self, hM0]
  have hQ : ∀ t ≤ L, (∀ t' ≤ t, x t' = x (t' % M)) ∧ (∀ t' < t, a t' = a (t' % M)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨fun t' ht' => by simp [show t' = 0 by omega], fun _ h => absurd h (by omega)⟩
    | succ t ih =>
      intro htL
      obtain ⟨ihx, iha⟩ := ih (by omega)
      by_cases htM : t + 1 ≤ M
      · exact ⟨fun t' ht' => hxM t' (by omega), fun t' ht' => by rw [Nat.mod_eq_of_lt (by omega)]⟩
      · obtain ⟨j, hj, hje⟩ := hback t (by omega)
        have hi : t % M < M := Nat.mod_lt _ (by omega)
        have hxt := ihx t le_rfl
        rcases ee_eq hje.symm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have hji : j = t % M := hD j (t % M) hj hi (h2.symm.trans hxt)
          have hat : a t = a (t % M) := hji ▸ h1
          have hxt1 : x (t + 1) = x ((t + 1) % M) := by
            rw [h3, hji, hxM (t % M + 1) (by omega), Nat.mod_add_mod]
          refine ⟨fun t' ht' => ?_, fun t' ht' => ?_⟩
          · rcases Nat.lt_or_ge t' (t + 1) with h | h
            · exact ihx t' (by omega)
            · rw [show t' = t + 1 by omega]; exact hxt1
          · rcases Nat.lt_or_ge t' t with h | h
            · exact iha t' h
            · rw [show t' = t by omega]; exact hat
        · exfalso
          have hjj : (t - 1) % M < M := Nat.mod_lt _ (by omega)
          have e1 : ((t - 1) % M + 1) % M = t % M := by
            rw [Nat.mod_add_mod, show t - 1 + 1 = t by omega]
          have e2 : (j + 1) % M = t % M := by
            apply hD _ _ (Nat.mod_lt _ (by omega)) hi
            rw [← hxM (j + 1) (by omega), ← hxt, h2]
          have hjeq : j = (t - 1) % M := mod_succ_inj hj hjj (e2.trans e1.symm)
          have ha1 : a (t - 1) = a j := by rw [hjeq]; exact iha (t - 1) (by omega)
          apply hcl' (t - 1) (by omega)
          rw [show t - 1 + 1 = t by omega, ha1]; exact h1
  obtain ⟨hQx, hQa⟩ := hQ L le_rfl
  have hDmod : ∀ u ≤ L, ∀ v ≤ L, (x u = x v ↔ u % M = v % M) := by
    intro u hu v hv
    rw [hQx u hu, hQx v hv]
    exact ⟨hD _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)), fun h => by rw [h]⟩
  refine ⟨M, by omega, Nat.dvd_of_mod_eq_zero ?_, hQa, hDmod⟩
  have := (hDmod L le_rfl 0 (by omega)).1 hcl
  simpa using this

lemma mod_succ_iff {M s' t : ℕ} : (s' + 1) % M = (t + 1) % M ↔ s' % M = t % M :=
  ⟨fun h => Nat.ModEq.add_right_cancel' 1 h, fun h => Nat.ModEq.add_right 1 h⟩

theorem gen_per (hcr : ∀ t < L, a ((t + 1) % L) ≠ bar (a t))
    {M : ℕ} (hM : 1 ≤ M) (hML : M ∣ L) (hL : 1 ≤ L) (hper : ∀ t < L, a t = a (t % M))
    (hker : ∀ u ≤ L, ∀ v ≤ L, (x u = x v ↔ u % M = v % M)) :
    (∀ s' < L, ∀ t < L, ∀ i p q, ee a x s' = Sum.inl (i, p) → ee a x t = Sum.inl (i, q) →
      (p.1 = q.1 ↔ p.2 = q.2)) ∧
    (∀ s' < L, ∀ j p, ee a x s' = Sum.inr (j, p) → ¬ p.IsDiag) ∧
    (∀ s' < L, ∀ t < L, ∀ j p q, ee a x s' = Sum.inr (j, p) → ee a x t = Sum.inr (j, q) →
      (∃ v, v ∈ p ∧ v ∈ q) → p = q) ∧
    (UU x L).card = (EE a x L).card := by
  have hML' : M ≤ L := Nat.le_of_dvd (by omega) hML
  have CRM : ∀ s' < L, ∀ t < L, t % M = (s' + 1) % M → a t ≠ bar (a s') := by
    intro s' hs t ht h heq
    have h1 := hcr (s' % M) (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hML')
    have key : a ((s' % M + 1) % L) = a t := by
      rw [hper _ (Nat.mod_lt _ (by omega)), Nat.mod_mod_of_dvd _ hML, Nat.mod_add_mod, ← h,
        ← hper t ht]
    rw [key, ← hper s' hs] at h1
    exact h1 heq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s' hs t ht i p q hp hq
    have k1 := hker s' (by omega) t (by omega)
    have k2 := hker (s' + 1) (by omega) (t + 1) (by omega)
    have k3 := hker (s' + 1) (by omega) t (by omega)
    have k4 := hker s' (by omega) (t + 1) (by omega)
    have c1 := CRM s' hs t ht
    have c2 := CRM t ht s' hs
    unfold ee at hp hq
    rcases hs' : a s' with ⟨i1, _ | _⟩ | j1 <;> rcases ht' : a t with ⟨i2, _ | _⟩ | j2 <;>
      rw [hs'] at hp c2 <;> rw [ht'] at hq c1 <;> rw [hs'] at c1 <;> rw [ht'] at c2 <;>
      simp only [ed, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq] at hp hq
    · obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl⟩ := hq
      show x s' = x t ↔ x (s' + 1) = x (t + 1)
      rw [k2, k1, mod_succ_iff]
    · obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl⟩ := hq
      show x s' = x (t + 1) ↔ x (s' + 1) = x t
      exact iff_of_false (fun h => c2 (k4.1 h) rfl) (fun h => c1 ((k3.1 h).symm) rfl)
    · obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl⟩ := hq
      show x (s' + 1) = x t ↔ x s' = x (t + 1)
      exact iff_of_false (fun h => c1 ((k3.1 h).symm) rfl) (fun h => c2 (k4.1 h) rfl)
    · obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl⟩ := hq
      show x (s' + 1) = x (t + 1) ↔ x s' = x t
      rw [k2, k1, mod_succ_iff]
  · intro s' hs j p hp hd
    have k := hker s' (by omega) (s' + 1) (by omega)
    have c := CRM s' hs s' hs
    unfold ee at hp
    rcases hs' : a s' with ⟨i1, _ | _⟩ | j1 <;> rw [hs'] at hp c <;>
      simp only [ed, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [Sym2.mk_isDiag_iff] at hd
    exact c (k.1 hd) rfl
  · intro s' hs t ht j p q hp hq hv
    have k1 := hker s' (by omega) t (by omega)
    have k2 := hker (s' + 1) (by omega) (t + 1) (by omega)
    have k3 := hker (s' + 1) (by omega) t (by omega)
    have k4 := hker s' (by omega) (t + 1) (by omega)
    have c1 := CRM s' hs t ht
    have c2 := CRM t ht s' hs
    unfold ee at hp hq
    rcases hs' : a s' with ⟨i1, _ | _⟩ | j1 <;> rcases ht' : a t with ⟨i2, _ | _⟩ | j2 <;>
      rw [hs'] at hp c2 <;> rw [ht'] at hq c1 <;> rw [hs'] at c1 <;> rw [ht'] at c2 <;>
      simp only [ed, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at hp hq
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨v, hv1, hv2⟩ := hv
    rw [Sym2.mem_iff] at hv1 hv2
    have same : s' % M = t % M → s(x s', x (s' + 1)) = s(x t, x (t + 1)) := fun h => by
      rw [k1.2 h, k2.2 (mod_succ_iff.2 h)]
    rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
    · exact same (k1.1 (h1.symm.trans h2))
    · exact absurd rfl (c2 (k4.1 (h1.symm.trans h2)))
    · exact absurd rfl (c1 (k3.1 (h1.symm.trans h2)).symm)
    · exact same (mod_succ_iff.1 (k2.1 (h1.symm.trans h2)))
  · have hcl : x L = x 0 := (hker L le_rfl 0 (by omega)).2 (by simp [Nat.mod_eq_zero_of_dvd hML])
    refine le_antisymm (gen_le hL hcr hcl) (le_trans (b := M) ?_ ?_)
    · have hsub : EE a x L ⊆ (range M).image (ee a x) := by
        intro p hp
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
        have ht := mem_range.1 ht
        have hm : t % M < M := Nat.mod_lt _ (by omega)
        have hmt : t % M ≤ t := Nat.mod_le _ _
        refine mem_image.2 ⟨t % M, mem_range.2 hm, ?_⟩
        have e1 : x (t % M) = x t := (hker _ (by omega) t (by omega)).2 (Nat.mod_mod _ _)
        have e2 : x (t % M + 1) = x (t + 1) :=
          (hker _ (by omega) (t + 1) (by omega)).2 (by rw [Nat.mod_add_mod])
        simp only [ee, e1, e2, ← hper t ht]
      calc (EE a x L).card ≤ ((range M).image (ee a x)).card := card_le_card hsub
        _ ≤ (range M).card := card_image_le
        _ = M := card_range M
    · have hsub : (range M).image x ⊆ UU x L := by
        intro y hy
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
        exact mem_UU (by have := mem_range.1 ht; omega)
      calc M = (range M).card := (card_range M).symm
        _ = ((range M).image x).card := by
          refine (card_image_of_injOn fun i hi j hj hij => ?_).symm
          have hi := mem_range.1 hi
          have hj := mem_range.1 hj
          have := (hker i (by omega) j (by omega)).1 hij
          rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
        _ ≤ (UU x L).card := card_le_card hsub

end Gen

section Bridge

variable {r s : ℕ}

/-- The letters of a nonempty word, read cyclically along `ℕ`. -/
def A (u : List (Lt r s)) (hne : u ≠ []) (t : ℕ) : Lt r s :=
  u.get ⟨t % u.length, Nat.mod_lt _ (List.length_pos_iff.2 hne)⟩

/-- A colouring read along `ℕ`. -/
def X {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : ℕ) : β := c ⟨min t L, by omega⟩

lemma get_A (u : List (Lt r s)) (hne : u ≠ []) (t : Fin u.length) : u.get t = A u hne t.val := by
  unfold A; congr 1; ext; simp [Nat.mod_eq_of_lt t.2]

lemma X_cs {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : Fin L) :
    c t.castSucc = X c t.val := by
  unfold X; congr 1; ext; simp

lemma X_succ {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : Fin L) :
    c t.succ = X c (t.val + 1) := by
  unfold X; congr 1; ext; simp

lemma X_fin {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : Fin (L + 1)) :
    c t = X c t.val := by
  unfold X; congr 1; ext; simp; omega

lemma ee_fin {β : Type*} (u : List (Lt r s)) (hne : u ≠ []) (c : Fin (u.length + 1) → β)
    (t : Fin u.length) :
    ee (A u hne) (X c) t.val = ed (u.get t) (c t.castSucc) (c t.succ) := by
  rw [ee, ← get_A, ← X_cs, ← X_succ]

lemma mem_Es {β : Type*} [DecidableEq β] (u : List (Lt r s)) (hne : u ≠ [])
    (c : Fin (u.length + 1) → β) (i : Fin r) (p : β × β) :
    p ∈ Es u c i ↔ ∃ t < u.length, ee (A u hne) (X c) t = Sum.inl (i, p) := by
  unfold Es
  simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t.val, t.2, by rw [ee_fin, ht]; rfl⟩
    · exact ⟨t.val, t.2, by rw [ee_fin, ht]; rfl⟩
  · rintro ⟨t, ht, h⟩
    have h' := ee_fin u hne c ⟨t, ht⟩
    simp only at h'
    rw [h'] at h
    rcases hl : u.get ⟨t, ht⟩ with ⟨i', _ | _⟩ | j <;> rw [hl] at h <;>
      simp only [ed, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq] at h
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨⟨t, ht⟩, hl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨⟨t, ht⟩, hl, rfl⟩

lemma mem_Ms {β : Type*} [DecidableEq β] (u : List (Lt r s)) (hne : u ≠ [])
    (c : Fin (u.length + 1) → β) (j : Fin s) (p : Sym2 β) :
    p ∈ Ms u c j ↔ ∃ t < u.length, ee (A u hne) (X c) t = Sum.inr (j, p) := by
  unfold Ms
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.val, t.2, by rw [ee_fin, ht]; rfl⟩
  · rintro ⟨t, ht, h⟩
    have h' := ee_fin u hne c ⟨t, ht⟩
    simp only at h'
    rw [h'] at h
    rcases hl : u.get ⟨t, ht⟩ with ⟨i', _ | _⟩ | j' <;> rw [hl] at h <;>
      simp only [ed, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨t, ht⟩, hl, rfl⟩

lemma nv_eq {L : ℕ} {β : Type*} [DecidableEq β] (c : Fin (L + 1) → β) :
    nv c = (UU (X c) L).card := by
  unfold nv UU
  congr 1
  ext y
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t.val, t.2, (X_fin c t).symm⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨⟨min t L, by omega⟩, rfl⟩

lemma Ecount_eq (u : List (Lt r s)) (hne : u ≠ [])
    (c : Fin (u.length + 1) → Fin (u.length + 1)) :
    Ecount u c = (EE (A u hne) (X c) u.length).card := by
  have h : EE (A u hne) (X c) u.length =
      (univ.biUnion fun i => (Es u c i).image fun p => (Sum.inl (i, p) : Edge r s _)) ∪
        (univ.biUnion fun j => (Ms u c j).image fun p => (Sum.inr (j, p) : Edge r s _)) := by
    ext e
    simp only [EE, mem_image, mem_range, mem_union, mem_biUnion, mem_univ, true_and,
      mem_Es u hne, mem_Ms u hne]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases he : ee (A u hne) (X c) t with ⟨i, p⟩ | ⟨j, p⟩
      · exact Or.inl ⟨i, p, ⟨t, ht, he⟩, rfl⟩
      · exact Or.inr ⟨j, p, ⟨t, ht, he⟩, rfl⟩
    · rintro (⟨i, p, ⟨t, ht, he⟩, rfl⟩ | ⟨j, p, ⟨t, ht, he⟩, rfl⟩)
      · exact ⟨t, ht, he⟩
      · exact ⟨t, ht, he⟩
  rw [h, card_union_of_disjoint, card_biUnion, card_biUnion]
  · unfold Ecount
    congr 1
    · refine sum_congr rfl fun i _ => (card_image_of_injective _ (fun p q h => ?_)).symm
      simpa using h
    · refine sum_congr rfl fun j _ => (card_image_of_injective _ (fun p q h => ?_)).symm
      simpa using h
  · intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro z hz hz'
    obtain ⟨p, -, rfl⟩ := mem_image.1 hz
    obtain ⟨q, -, h⟩ := mem_image.1 hz'
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact hij h.1.symm
  · intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro z hz hz'
    obtain ⟨p, -, rfl⟩ := mem_image.1 hz
    obtain ⟨q, -, h⟩ := mem_image.1 hz'
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    exact hij h.1.symm
  · rw [disjoint_left]
    intro z hz hz'
    obtain ⟨i, -, hz⟩ := mem_biUnion.1 hz
    obtain ⟨j, -, hz'⟩ := mem_biUnion.1 hz'
    obtain ⟨p, -, rfl⟩ := mem_image.1 hz
    obtain ⟨q, -, h⟩ := mem_image.1 hz'
    simp at h

lemma hcl_of_good (u : List (Lt r s)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (h : Good u c) : X c u.length = X c 0 := by
  have := h.2.2
  rw [X_fin c 0, X_fin c (Fin.last _)] at this
  simpa using this.symm

lemma hcr_of (u : List (Lt r s)) (hne : u ≠ []) (h : CycRed u) :
    ∀ t < u.length, A u hne ((t + 1) % u.length) ≠ bar (A u hne t) := by
  intro t ht
  have := h ⟨t, ht⟩
  rw [get_A u hne, get_A u hne] at this
  exact this

end Bridge

variable {r s : ℕ}

theorem nv_le_Ecount (u : List (Lt r s)) (hne : u ≠ []) (hc : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcG : c ∈ CG u) :
    nv c ≤ Ecount u c := by
  have hc' := (mem_filter.1 hcG).2
  rw [nv_eq, Ecount_eq u hne c]
  exact gen_le (List.length_pos_iff.2 hne) (hcr_of u hne hc) (hcl_of_good u c hc')

section Periods

/-- The periodic colouring `t ↦ t mod M`. -/
def col (L M : ℕ) : Fin (L + 1) → Fin (L + 1) :=
  fun t => ⟨t.val % M, lt_of_le_of_lt (Nat.mod_le _ _) t.2⟩

lemma canon_eq_of_ker {n : ℕ} {α β : Type*} [DecidableEq α] [DecidableEq β] (x : Fin n → α)
    (y : Fin n → β) (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_col (L M : ℕ) : canon (col L M) = col L M := by
  funext t
  unfold canon
  apply le_antisymm
  · apply Finset.min'_le
    simp [col]
  · apply Finset.le_min'
    intro y hy
    simp only [mem_filter, mem_univ, true_and, col, Fin.mk.injEq] at hy
    rw [Fin.le_iff_val_le_val]
    show t.val % M ≤ y.val
    rw [← hy]; exact Nat.mod_le _ _

lemma col_ne {L M M' : ℕ} (hM : 1 ≤ M) (hlt : M < M') (hML : M ≤ L) : col L M ≠ col L M' := by
  intro h
  have := congrArg Fin.val (congrFun h ⟨M, by omega⟩)
  simp only [col, Nat.mod_self, Nat.mod_eq_of_lt hlt] at this
  omega

lemma per_iff {β : Type*} (a : ℕ → β) {L M : ℕ} (hM : 1 ≤ M) (hML : M ∣ L) (hL : 1 ≤ L) :
    (∀ t < L, a t = a (t % M)) ↔ ∀ t < L, a ((t + M) % L) = a t := by
  have hML' : M ≤ L := Nat.le_of_dvd (by omega) hML
  constructor
  · intro h t ht
    rw [h _ (Nat.mod_lt _ (by omega)), Nat.mod_mod_of_dvd _ hML, Nat.add_mod_right, ← h t ht]
  · intro h t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      by_cases htM : t < M
      · rw [Nat.mod_eq_of_lt htM]
      · have h1 := h (t - M) (by omega)
        rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt ht] at h1
        rw [h1, ih (t - M) (by omega) (by omega), ← Nat.mod_eq_sub_mod (by omega)]

end Periods

theorem card_eq_per (u : List (Lt r s)) (hne : u ≠ []) (hc : CycRed u) :
    ((CG u).filter fun c => nv c = Ecount u c).card = per u := by
  have hL : 1 ≤ u.length := List.length_pos_iff.2 hne
  have hcrA := hcr_of u hne hc
  have hperA : ∀ ℓ, (∀ t : Fin u.length,
      u.get ⟨(t.val + ℓ) % u.length, Nat.mod_lt _ (by omega)⟩ = u.get t) ↔
        ∀ t < u.length, A u hne ((t + ℓ) % u.length) = A u hne t := by
    intro ℓ
    constructor
    · intro h t ht
      have := h ⟨t, ht⟩
      rwa [get_A u hne, get_A u hne] at this
    · intro h t
      rw [get_A u hne, get_A u hne]
      exact h t.val t.2
  unfold per
  symm
  refine Finset.card_bij (fun ℓ _ => col u.length ℓ) ?_ ?_ ?_
  · intro M hMmem
    obtain ⟨hMd, hMp⟩ := mem_filter.1 hMmem
    obtain ⟨hML, -⟩ := Nat.mem_divisors.1 hMd
    have hM : 1 ≤ M := Nat.pos_of_dvd_of_pos hML (by omega)
    have hper := (per_iff (A u hne) hM hML hL).2 ((hperA M).1 hMp)
    have hker : ∀ s' ≤ u.length, ∀ t ≤ u.length,
        (X (col u.length M) s' = X (col u.length M) t ↔ s' % M = t % M) := by
      intro s' hs t ht
      simp [X, col, Fin.ext_iff, min_eq_left hs, min_eq_left ht]
    obtain ⟨hfold, hnd, hdisj, hcard⟩ := gen_per hcrA hM hML hL hper hker
    have hgood : Good u (col u.length M) := by
      refine ⟨fun i p hp q hq => ?_, fun j => ⟨fun p hp => ?_, fun p hp q hq hv => ?_⟩, ?_⟩
      · rw [mem_Es u hne] at hp hq
        obtain ⟨s', hs, hes⟩ := hp
        obtain ⟨t, ht, het⟩ := hq
        exact hfold s' hs t ht i p q hes het
      · rw [mem_Ms u hne] at hp
        obtain ⟨s', hs, hes⟩ := hp
        exact hnd s' hs j p hes
      · rw [mem_Ms u hne] at hp hq
        obtain ⟨s', hs, hes⟩ := hp
        obtain ⟨t, ht, het⟩ := hq
        exact hdisj s' hs t ht j p q hes het hv
      · ext; simp [col, Nat.mod_eq_zero_of_dvd hML]
    refine mem_filter.2 ⟨mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, canon_col _ _⟩, hgood⟩, ?_⟩
    rw [nv_eq, Ecount_eq u hne]
    exact hcard
  · intro a ha b hb hab
    have ha' := Nat.mem_divisors.1 (mem_filter.1 ha).1
    have hb' := Nat.mem_divisors.1 (mem_filter.1 hb).1
    have hle : ∀ m, m ∣ u.length → 1 ≤ m ∧ m ≤ u.length := fun m hm =>
      ⟨Nat.pos_of_dvd_of_pos hm (by omega), Nat.le_of_dvd (by omega) hm⟩
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact col_ne (hle a ha'.1).1 h (hle a ha'.1).2 hab
    · exact col_ne (hle b hb'.1).1 h (hle b hb'.1).2 hab.symm
  · intro c hcmem
    obtain ⟨hcG, hVE⟩ := mem_filter.1 hcmem
    have hc' := mem_filter.1 hcG
    have hcan : canon c = c := (mem_filter.1 hc'.1).2
    rw [nv_eq, Ecount_eq u hne c] at hVE
    obtain ⟨M, hM, hML, hper, hker⟩ := gen_struct hL hcrA (hcl_of_good u c hc'.2) hVE
    refine ⟨M, mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hML, by omega⟩,
      (hperA M).2 ((per_iff (A u hne) hM hML hL).1 hper)⟩, ?_⟩
    calc col _ M = canon (col _ M) := (canon_col _ _).symm
      _ = canon c := by
        refine canon_eq_of_ker _ _ fun s' t => ?_
        rw [X_fin c s', X_fin c t, hker s'.val (by omega) t.val (by omega), Fin.ext_iff]
        rfl
      _ = c := hcan

end BordenaveCollins.PartK

end
end

section
/-!
# The statements proved in Part K, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem nv_le_Ecount (u : List (Lt r s)) (hne : u ≠ []) (hc : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcG : c ∈ CG u) :
    nv c ≤ Ecount u c :=
  PartK.nv_le_Ecount u hne hc c hcG

theorem card_eq_per (u : List (Lt r s)) (hne : u ≠ []) (hc : CycRed u) :
    ((CG u).filter fun c => nv c = Ecount u c).card = per u :=
  PartK.card_eq_per u hne hc

end BordenaveCollins

end
end

section
/-!
# Part F2, toolkit: reduced words in `F_r * Γ_s`

General word lemmas built on `BordenaveCollins.nf_exists` and `BordenaveCollins.genL_bar`.
-/

open Finset

noncomputable section

namespace BordenaveCollins.PartF2

variable {r s : ℕ}

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

theorem gid_cancel {H : Type*} [Group H] (x a y : H) : x * (a * (a⁻¹ * y)) = x * y := by group

theorem gid_conj_inv {H : Type*} [Group H] (p X : H) : X = p⁻¹ * (p * X * p⁻¹) * p⁻¹⁻¹ := by
  group

theorem gid_rot1 {H : Type*} [Group H] (x c : H) : c * x⁻¹ = x * (x⁻¹ * c) * x⁻¹ := by group

theorem gid_rot2 {H : Type*} [Group H] (x d : H) : x * d = x * (d * x) * x⁻¹ := by group

theorem gid_conj_mul {H : Type*} [Group H] (x w u : H) :
    (x * w) * u * (x * w)⁻¹ = x * (w * u * w⁻¹) * x⁻¹ := by group

theorem gid_sq_conj {H : Type*} [Group H] (p c : H) (h : p * c * p⁻¹ * (p * c * p⁻¹) = 1) :
    c * c = 1 := by
  have : c * c = p⁻¹ * (p * c * p⁻¹ * (p * c * p⁻¹)) * p := by group
  rw [this, h]; group

theorem gid_conj_eq_one {H : Type*} [Group H] (p c : H) (h : p * c * p⁻¹ = 1) : c = 1 := by
  have : c = p⁻¹ * (p * c * p⁻¹) * p := by group
  rw [this, h]; group

theorem gid_conj_sq {H : Type*} [Group H] (p c : H) (h : c * c = 1) :
    p * c * p⁻¹ * (p * c * p⁻¹) = 1 := by
  have : p * c * p⁻¹ * (p * c * p⁻¹) = p * (c * c) * p⁻¹ := by group
  rw [this, h]; group

theorem gid_conj_pow_sq {H : Type*} [Group H] (a z : H) (k : ℕ)
    (h : a * z ^ k * a⁻¹ * (a * z ^ k * a⁻¹) = 1) : z ^ (k + k) = 1 := by
  rw [pow_add]
  exact gid_sq_conj a (z ^ k) h

/-! ## `bar` -/

theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem bar_inj {a b : Lt r s} (h : bar a = bar b) : a = b := by
  have := congrArg bar h
  simpa [bar_bar] using this

/-! ## `wprod` -/

@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := by simp [wprod]

theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) : wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

theorem wprod_singleton (a : Lt r s) : wprod [a] = genL a := by simp [wprod]

theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The normal form -/

/-- The normal form (reduced word) of a group element. -/
def nf (g : G r s) : List (Lt r s) := Classical.choose (nf_exists r s) g

theorem nf_red (g : G r s) : Red (nf g) := (Classical.choose_spec (nf_exists r s)).1 g

theorem wprod_nf (g : G r s) : wprod (nf g) = g := (Classical.choose_spec (nf_exists r s)).2.1 g

theorem nf_wprod {u : List (Lt r s)} (h : Red u) : nf (wprod u) = u :=
  (Classical.choose_spec (nf_exists r s)).2.2.1 u h

theorem len_eq (g : G r s) : len g = (nf g).length :=
  (Classical.choose_spec (nf_exists r s)).2.2.2 g

theorem red_nil : Red ([] : List (Lt r s)) := List.IsChain.nil

theorem red_left {u v : List (Lt r s)} (h : Red (u ++ v)) : Red u := List.IsChain.left_of_append h

theorem nf_one : nf (1 : G r s) = [] := by
  have := nf_wprod (r := r) (s := s) (u := []) red_nil
  simpa using this

theorem nf_eq_nil_iff {g : G r s} : nf g = [] ↔ g = 1 := by
  constructor
  · intro h
    rw [← wprod_nf g, h, wprod_nil]
  · rintro rfl
    exact nf_one

theorem eq_nil_of_red_of_wprod {u : List (Lt r s)} (hu : Red u) (h : wprod u = 1) : u = [] := by
  rw [← nf_wprod hu, h, nf_one]

theorem len_le (u : List (Lt r s)) : len (wprod u) ≤ u.length := Nat.sInf_le ⟨u, rfl, rfl⟩

/-! ## The inverse word -/

/-- The inverse word: reversed, with `bar` applied. -/
def inv (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

@[simp] theorem inv_nil : inv ([] : List (Lt r s)) = [] := rfl

theorem inv_cons (a : Lt r s) (u : List (Lt r s)) : inv (a :: u) = inv u ++ [bar a] := by
  simp [inv]

@[simp] theorem length_inv (u : List (Lt r s)) : (inv u).length = u.length := by simp [inv]

theorem wprod_inv (u : List (Lt r s)) : wprod (inv u) = (wprod u)⁻¹ := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [inv_cons, wprod_append, ih, wprod_cons a u, wprod_singleton, genL_bar]
    exact (mul_inv_rev (G := G r s) _ _).symm

theorem wprod_conj_cons (p : Lt r s) (W : List (Lt r s)) :
    wprod (p :: W ++ [bar p]) = genL p * wprod W * (genL p)⁻¹ := by
  rw [List.cons_append, wprod_cons, wprod_append, wprod_singleton, genL_bar]
  exact (mul_assoc _ _ _).symm

/-! ## Non-reduced words are not shortest -/

theorem not_red_split {u : List (Lt r s)} (h : ¬ Red u) :
    ∃ x a y, u = x ++ a :: bar a :: y := by
  induction u with
  | nil => exact absurd red_nil h
  | cons a t ih =>
    cases t with
    | nil => exact absurd (List.isChain_singleton a) h
    | cons b t =>
      by_cases hb : b = bar a
      · exact ⟨[], a, t, by simp [hb]⟩
      · have : ¬ Red (b :: t) := fun h' => h (List.isChain_cons_cons.2 ⟨hb, h'⟩)
        obtain ⟨x, c, y, e⟩ := ih this
        exact ⟨a :: x, c, y, by simp [e]⟩

/-- A word of minimal length is reduced. -/
theorem red_of_length {u : List (Lt r s)} {g : G r s} (h : wprod u = g)
    (hl : u.length = len g) : Red u := by
  by_contra hr
  obtain ⟨x, a, y, rfl⟩ := not_red_split hr
  have h2 : wprod (x ++ y) = g := by
    rw [← h, wprod_append, wprod_append, wprod_cons, wprod_cons, genL_bar]
    exact (gid_cancel (H := G r s) _ _ _).symm
  have h3 := len_le (x ++ y)
  rw [h2] at h3
  simp at hl h3
  omega

/-- A word of length `len` of its product is the normal form. -/
theorem eq_nf_of_length {u : List (Lt r s)} {g : G r s} (h : wprod u = g)
    (hl : u.length = len g) : nf g = u := by
  rw [← h]
  exact nf_wprod (red_of_length h hl)

/-! ## Repeated words -/

/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

theorem rep_add (Z : List (Lt r s)) (k l : ℕ) : rep Z (k + l) = rep Z k ++ rep Z l := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.add_right_comm, rep_succ, rep_succ, ih, List.append_assoc]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

theorem wprod_rep (Z : List (Lt r s)) (k : ℕ) : wprod (rep Z k) = wprod Z ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, wprod_append, ih, pow_succ']

theorem take_rep_succ (Z : List (Lt r s)) (k : ℕ) : (rep Z (k + 1)).take Z.length = Z := by
  rw [rep_succ, List.take_left]

theorem rep_getElem? (Z : List (Lt r s)) (k i : ℕ) (hi : i < k * Z.length) :
    (rep Z k)[i]? = Z[i % Z.length]? := by
  induction k generalizing i with
  | zero => simp at hi
  | succ k ih =>
    rw [rep_succ]
    by_cases h : i < Z.length
    · rw [List.getElem?_append_left h, Nat.mod_eq_of_lt h]
    · have h' : Z.length ≤ i := by omega
      rw [List.getElem?_append_right h', ih _ (by rw [Nat.succ_mul] at hi; omega),
        ← Nat.mod_eq_sub_mod h']

theorem rep_getElem (Z : List (Lt r s)) (k i : ℕ) (h : i < (rep Z k).length)
    (h' : i % Z.length < Z.length) : (rep Z k)[i] = Z[i % Z.length] := by
  have := rep_getElem? Z k i (by simpa using h)
  rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h'] at this
  exact Option.some.inj this

/-- If `Z ++ Z` is reduced then all powers of `Z` are reduced. -/
theorem red_rep {Z : List (Lt r s)} (h : Red (Z ++ Z)) (k : ℕ) : Red (rep Z k) := by
  by_cases hZ : Z = []
  · subst hZ
    rw [rep_nil]
    exact red_nil
  induction k with
  | zero => rw [rep_zero]; exact red_nil
  | succ k ih =>
    cases k with
    | zero => simpa [rep_succ] using red_left h
    | succ k =>
      rw [rep_succ]
      rw [Red, List.isChain_append] at h ⊢
      refine ⟨h.1, ih, ?_⟩
      intro x hx y hy
      rw [rep_succ, List.head?_append_of_ne_nil _ hZ] at hy
      exact h.2.2 x hx y hy

/-- `CycRed` gives that the square is reduced. -/
theorem red_sq_of_cycRed {u : List (Lt r s)} (hc : CycRed u) : Red (u ++ u) := by
  have e : u ++ u = rep u 2 := by simp [rep_succ]
  rw [e, Red, List.isChain_iff_getElem]
  intro i hi
  have hL : 0 < u.length := by
    rcases Nat.eq_zero_or_pos u.length with h0 | h0
    · simp [h0] at hi
    · exact h0
  have h1 := rep_getElem u 2 i (by omega) (Nat.mod_lt _ hL)
  have h2 := rep_getElem u 2 (i + 1) hi (Nat.mod_lt _ hL)
  rw [h1, h2]
  have := hc ⟨i % u.length, Nat.mod_lt _ hL⟩
  simp only [List.get_eq_getElem] at this
  convert this using 2
  simp [Nat.add_mod]

/-- If `Z ++ Z` is reduced and `Z ≠ []`, the element `wprod Z` has infinite order. -/
theorem wprod_pow_ne_one {Z : List (Lt r s)} (h : Red (Z ++ Z)) (hZ : Z ≠ []) {k : ℕ}
    (hk : k ≠ 0) : wprod Z ^ k ≠ 1 := by
  intro h1
  rw [← wprod_rep] at h1
  have := congrArg List.length (eq_nil_of_red_of_wprod (red_rep h k) h1)
  simp at this
  rcases this with h | h
  · exact hk h
  · exact hZ h

/-! ## Cyclic rotation of a cyclically reduced word -/

theorem red_sq_rot1 {c : Lt r s} {C : List (Lt r s)} (h : Red ((c :: C) ++ (c :: C))) :
    Red ((C ++ [c]) ++ (C ++ [c])) :=
  (red_rep h 3).infix ⟨[c], C, by simp [rep_succ]⟩

theorem red_sq_rot2 {d : Lt r s} {D : List (Lt r s)} (h : Red ((D ++ [d]) ++ (D ++ [d]))) :
    Red ((d :: D) ++ (d :: D)) :=
  (red_rep h 3).infix ⟨D, [d], by simp [rep_succ]⟩

/-! ## Uniqueness of the conjugating prefix -/

/-- `M` does not begin with a letter and end with its inverse. -/
def NB (M : List (Lt r s)) : Prop := ∀ p N, M ≠ p :: (N ++ [bar p])

theorem nb_of_red_sq {M : List (Lt r s)} (h : Red (M ++ M)) : NB M := by
  intro p N e
  subst e
  have h2 : Red [bar p, p] := h.infix ⟨p :: N, N ++ [bar p], by simp⟩
  exact (List.isChain_pair.1 h2) (bar_bar p).symm

theorem decomp_unique {A P M C : List (Lt r s)} (hM : NB M) (hC : NB C)
    (h : A ++ M ++ inv A = P ++ C ++ inv P) : A = P ∧ M = C := by
  induction A generalizing P with
  | nil =>
    cases P with
    | nil => simpa using h
    | cons p P =>
      exfalso
      exact hM p (P ++ C ++ inv P) (by simpa [inv_cons] using h)
  | cons a A ih =>
    cases P with
    | nil =>
      exfalso
      exact hC a (A ++ M ++ inv A) (by simpa [inv_cons] using h.symm)
    | cons p P =>
      simp only [inv_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have h' : (A ++ M ++ inv A) ++ [bar a] = (P ++ C ++ inv P) ++ [bar a] := by
        simpa using h
      obtain ⟨rfl, rfl⟩ := ih (List.append_cancel_right h')
      exact ⟨rfl, rfl⟩

/-- A reduced expression `g = a z^k a⁻¹` (length equation) is a concatenation of normal forms. -/
theorem nf_of_triple {g a z : G r s} {k : ℕ} (hg : g = a * z ^ k * a⁻¹)
    (hl : len g = 2 * len a + k * len z) : nf g = nf a ++ rep (nf z) k ++ inv (nf a) := by
  apply eq_nf_of_length
  · rw [wprod_append, wprod_append, wprod_inv, wprod_rep, wprod_nf, wprod_nf, hg]
  · rw [hl, len_eq a, len_eq z]
    simp
    ring

/-- In a reduced expression `g = a z^k a⁻¹` with `k ≥ 2`, the word of `z` is cyclically
reduced. -/
theorem red_sq_of_triple {g a z : G r s} {k : ℕ} (hk : 2 ≤ k) (hg : g = a * z ^ k * a⁻¹)
    (hl : len g = 2 * len a + k * len z) : Red (nf z ++ nf z) := by
  have h := nf_red g
  rw [nf_of_triple hg hl] at h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine h.infix ⟨nf a, rep (nf z) k ++ inv (nf a), ?_⟩
  rw [show 2 + k = k + 1 + 1 by ring, rep_succ, rep_succ]
  simp

/-! ## Conjugates of a cyclically reduced word -/

/-- `g` has normal form `P ++ C ++ inv P` with `C` a cyclically reduced rotation of `u`. -/
def Dec (u : List (Lt r s)) (g : G r s) : Prop :=
  ∃ P C : List (Lt r s), C ≠ [] ∧ Red (C ++ C) ∧ Red (P ++ C ++ inv P) ∧
    wprod (P ++ C ++ inv P) = g ∧ C ~r u

theorem dec_step {u : List (Lt r s)} {g : G r s} (x : Lt r s) (h : Dec u g) :
    Dec u (genL x * g * (genL x)⁻¹) := by
  obtain ⟨P, C, hne, hCC, hred, rfl, hrot⟩ := h
  cases P with
  | cons p P =>
    by_cases hx : x = bar p
    · subst hx
      refine ⟨P, C, hne, hCC, ?_, ?_, hrot⟩
      · exact hred.infix ⟨[p], [bar p], by simp [inv_cons]⟩
      · have e : (p :: P) ++ C ++ inv (p :: P) = p :: (P ++ C ++ inv P) ++ [bar p] := by
          simp [inv_cons]
        rw [e, wprod_conj_cons, genL_bar]
        exact gid_conj_inv (H := G r s) _ _
    · refine ⟨x :: p :: P, C, hne, hCC, ?_, ?_, hrot⟩
      · have e : (x :: p :: P) ++ C ++ inv (x :: p :: P) =
            (x :: ((p :: P) ++ C ++ inv (p :: P))) ++ [bar x] := by
          simp [inv_cons]
        rw [e, Red, List.isChain_append]
        refine ⟨List.isChain_cons_cons.2 ⟨?_, hred⟩, List.isChain_singleton _, ?_⟩
        · intro h
          exact hx (by rw [h, bar_bar])
        · intro a ha b hb
          simp [inv_cons] at ha hb
          subst hb
          have ha' : a = bar p := by
            have e2 : p :: (P ++ (C ++ (inv P ++ [bar p]))) =
                (p :: (P ++ (C ++ inv P))) ++ [bar p] := by simp
            rw [e2, List.getLast?_concat] at ha
            exact (Option.some.inj ha).symm
          subst ha'
          intro h
          exact hx (bar_inj h)
      · have e : (x :: p :: P) ++ C ++ inv (x :: p :: P) =
            x :: ((p :: P) ++ C ++ inv (p :: P)) ++ [bar x] := by
          simp [inv_cons]
        rw [e, wprod_conj_cons]
  | nil =>
    simp only [inv_nil, List.nil_append, List.append_nil] at hred ⊢
    by_cases h1 : ∃ C', C = bar x :: C'
    · obtain ⟨C', rfl⟩ := h1
      refine ⟨[], C' ++ [bar x], by simp, red_sq_rot1 hCC, ?_, ?_, ?_⟩
      · simpa using red_left (red_sq_rot1 hCC)
      · rw [inv_nil, List.append_nil, List.nil_append]
        rw [wprod_append, wprod_singleton, wprod_cons, genL_bar]
        exact gid_rot1 (H := G r s) _ _
      · exact (List.isRotated_concat _ _).trans hrot
    · by_cases h2 : ∃ D, C = D ++ [x]
      · obtain ⟨D, rfl⟩ := h2
        refine ⟨[], x :: D, by simp, red_sq_rot2 hCC, ?_, ?_, ?_⟩
        · simpa using red_left (red_sq_rot2 hCC)
        · rw [inv_nil, List.append_nil, List.nil_append]
          rw [wprod_append, wprod_singleton, wprod_cons]
          exact gid_rot2 (H := G r s) _ _
        · exact (List.isRotated_concat x D).symm.trans hrot
      · refine ⟨[x], C, hne, hCC, ?_, ?_, hrot⟩
        · have e : [x] ++ C ++ inv [x] = (x :: C) ++ [bar x] := by simp [inv]
          rw [e, Red, List.isChain_append]
          refine ⟨List.isChain_cons.2 ⟨?_, hred⟩, List.isChain_singleton _, ?_⟩
          · intro y hy hyx
            obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 hy
            exact h1 ⟨t, by rw [ht, hyx]⟩
          · intro a ha b hb
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
            subst hb
            obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 ha
            intro h
            have hax : x = a := bar_inj h
            subst hax
            cases ys with
            | nil =>
              simp at hys
              exact hne hys
            | cons y ys =>
              simp only [List.cons_append, List.cons.injEq] at hys
              exact h2 ⟨ys, hys.2⟩
        · have e : [x] ++ C ++ inv [x] = x :: C ++ [bar x] := by simp [inv]
          rw [e, wprod_conj_cons]

/-- Every conjugate of a cyclically reduced word has normal form `P ++ C ++ inv P` with `C` a
rotation of the word. -/
theorem dec_conj {u : List (Lt r s)} (hne : u ≠ []) (hc : Red (u ++ u)) (a : G r s) :
    Dec u (a * wprod u * a⁻¹) := by
  have key : ∀ w : List (Lt r s), Dec u (wprod w * wprod u * (wprod w)⁻¹) := by
    intro w
    induction w with
    | nil =>
      exact ⟨[], u, hne, hc, by simpa using red_left hc, by simp, List.IsRotated.refl _⟩
    | cons x w ih =>
      have := dec_step x ih
      convert this using 1
      rw [wprod_cons]
      exact gid_conj_mul (H := G r s) _ _ _
  have := key (nf a)
  rwa [wprod_nf] at this

end BordenaveCollins.PartF2

end
end

section
/-!
# Part F2: the first-order coefficient `cfun` on conjugates of cyclically reduced words and
of the involutions `m_j`
-/

open Finset
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartF2

variable {r s : ℕ}

/-! ## Periods -/

/-- `ℓ` is a cyclic period of `u`. -/
def Pd (u : List (Lt r s)) (ℓ : ℕ) : Prop :=
  ∀ t, t < u.length → u[(t + ℓ) % u.length]? = u[t]?

theorem per_eq (u : List (Lt r s)) : per u = ((Nat.divisors u.length).filter (Pd u)).card := by
  unfold per
  apply congrArg Finset.card
  ext ℓ
  simp only [Finset.mem_filter]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h t ht
    have := h ⟨t, ht⟩
    simp only [List.get_eq_getElem] at this
    rw [List.getElem?_eq_getElem ht, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega)), this]
  · intro h t
    have := h t.1 t.2
    rw [List.getElem?_eq_getElem t.2,
      List.getElem?_eq_getElem (Nat.mod_lt _ (by have := t.2; omega))] at this
    simpa using this

theorem pd_rotate {u : List (Lt r s)} {ℓ : ℕ} (h : Pd u ℓ) (n : ℕ) : Pd (u.rotate n) ℓ := by
  intro t ht
  rw [List.length_rotate] at ht ⊢
  have hL : 0 < u.length := by omega
  rw [List.getElem?_rotate (Nat.mod_lt _ hL), List.getElem?_rotate ht]
  have := h ((t + n) % u.length) (Nat.mod_lt _ hL)
  rw [← this]
  have e : ((t + ℓ) % u.length + n) % u.length = ((t + n) % u.length + ℓ) % u.length := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_right_comm]
  rw [e]

/-- `per` is invariant under rotation. -/
theorem per_rot {u v : List (Lt r s)} (h : u ~r v) : per u = per v := by
  rw [per_eq, per_eq]
  have hl : u.length = v.length := h.perm.length_eq
  rw [hl]
  congr 1
  apply Finset.filter_congr
  intro ℓ _
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := List.IsRotated.symm ⟨n, hn⟩
  exact ⟨fun h => hn ▸ pd_rotate h n, fun h => hm ▸ pd_rotate h m⟩

theorem pd_of_rep {Z : List (Lt r s)} (hZ : Z ≠ []) (k : ℕ) : Pd (rep Z k) Z.length := by
  intro t ht
  have hZ' : 0 < Z.length := List.length_pos_iff.2 hZ
  rw [length_rep] at ht ⊢
  rw [rep_getElem? Z k _ (Nat.mod_lt _ (by omega)), rep_getElem? Z k t ht]
  congr 1
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro_left k rfl), Nat.add_mod_right]

theorem pd_mod {C : List (Lt r s)} {ℓ : ℕ} (h : Pd C ℓ) (hℓ : 0 < ℓ) :
    ∀ i, i < C.length → C[i]? = C[i % ℓ]? := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hlt : i < ℓ
    · rw [Nat.mod_eq_of_lt hlt]
    · have h1 := h (i - ℓ) (by omega)
      have e : (i - ℓ + ℓ) % C.length = i := by
        rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hi]
      rw [e] at h1
      rw [h1, ih (i - ℓ) (by omega) (by omega), ← Nat.mod_eq_sub_mod (by omega)]

theorem rep_of_pd {C : List (Lt r s)} {ℓ : ℕ} (h : Pd C ℓ) (hd : ℓ ∣ C.length) (hℓ : 0 < ℓ) :
    rep (C.take ℓ) (C.length / ℓ) = C := by
  rcases Nat.eq_zero_or_pos C.length with h0 | hL
  · have : C = [] := List.length_eq_zero_iff.1 h0
    subst this
    simp
  have hle : ℓ ≤ C.length := Nat.le_of_dvd hL hd
  have hlen : (C.take ℓ).length = ℓ := by rw [List.length_take]; omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i < C.length
  · rw [rep_getElem? _ _ _ (by rw [hlen, Nat.div_mul_cancel hd]; exact hi), hlen,
      pd_mod h hℓ i hi, List.getElem?_take_of_lt (Nat.mod_lt _ hℓ)]
  · rw [List.getElem?_eq_none (by rw [length_rep, hlen, Nat.div_mul_cancel hd]; omega),
      List.getElem?_eq_none (by omega)]

/-! ## The triples of `cfun` -/

/-- The triples `(k, z, a)` counted by `cfun g`. -/
abbrev Tr (g : G r s) : Type :=
  {t : ℕ × G r s × G r s // 2 ≤ t.1 ∧ t.2.1 ≠ 1 ∧
      g = t.2.2 * t.2.1 ^ t.1 * t.2.2⁻¹ ∧ len g = 2 * len t.2.2 + t.1 * len t.2.1}

theorem cfun_of_not {g : G r s} (h : ¬ (g ≠ 1 ∧ g * g = 1)) : cfun g = (Nat.card (Tr g) : ℤ) := by
  unfold cfun
  rw [if_neg h, sub_zero]

theorem cfun_of_inv {g : G r s} (h : g ≠ 1 ∧ g * g = 1) :
    cfun g = (Nat.card (Tr g) : ℤ) - 1 := by
  unfold cfun
  rw [if_pos h]

theorem triple_facts {g : G r s} {P C : List (Lt r s)} (hCC : Red (C ++ C))
    (hnf : nf g = P ++ C ++ inv P) {k : ℕ} {z a : G r s} (hk : 2 ≤ k)
    (hg : g = a * z ^ k * a⁻¹) (hl : len g = 2 * len a + k * len z) :
    nf a = P ∧ rep (nf z) k = C := by
  have h1 := nf_of_triple hg hl
  have h2 := red_sq_of_triple hk hg hl
  rw [hnf] at h1
  have hNB : NB (rep (nf z) k) := nb_of_red_sq (by rw [← rep_add]; exact red_rep h2 _)
  obtain ⟨e1, e2⟩ := decomp_unique (nb_of_red_sq hCC) hNB h1
  exact ⟨e1.symm, e2.symm⟩

/-- The triples of an element with cyclically reduced core `C` correspond to the proper
periods of `C`. -/
theorem card_triples {g : G r s} {P C : List (Lt r s)} (hne : C ≠ []) (hCC : Red (C ++ C))
    (hnf : nf g = P ++ C ++ inv P) :
    Nat.card (Tr g) = (((Nat.divisors C.length).filter (Pd C)).erase C.length).card := by
  set S := ((Nat.divisors C.length).filter (Pd C)).erase C.length with hS
  have hL : 0 < C.length := List.length_pos_iff.2 hne
  rw [← Nat.card_eq_finsetCard S]
  have memS : ∀ t : Tr g, C.length / t.1.1 ∈ S ∧ nf t.1.2.2 = P ∧ rep (nf t.1.2.1) t.1.1 = C ∧
      (nf t.1.2.1).length = C.length / t.1.1 ∧ t.1.1 * (C.length / t.1.1) = C.length := by
    rintro ⟨⟨k, z, a⟩, hk, hz, hg, hl⟩
    dsimp only at hk hz hg hl ⊢
    obtain ⟨e1, e2⟩ := triple_facts hCC hnf hk hg hl
    have hZ : nf z ≠ [] := fun h => hz (nf_eq_nil_iff.1 h)
    have hZ' : 0 < (nf z).length := List.length_pos_iff.2 hZ
    have hlen : C.length = k * (nf z).length := by rw [← e2, length_rep]
    have hdiv : C.length / k = (nf z).length := by
      rw [hlen]; exact Nat.mul_div_cancel_left _ (by omega)
    refine ⟨?_, e1, e2, hdiv.symm, by rw [hdiv, hlen]⟩
    rw [hdiv, hS, Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨?_, ⟨⟨k, by rw [hlen, mul_comm]⟩, by omega⟩, ?_⟩
    · intro h
      have : 2 * (nf z).length ≤ k * (nf z).length := Nat.mul_le_mul_right _ hk
      omega
    · have := pd_of_rep hZ k
      rwa [e2] at this
  refine Nat.card_congr (Equiv.ofBijective (fun t => ⟨C.length / t.1.1, (memS t).1⟩) ⟨?_, ?_⟩)
  · intro t1 t2 h
    have h' : C.length / t1.1.1 = C.length / t2.1.1 := congrArg Subtype.val h
    obtain ⟨_, a1, z1, l1, m1⟩ := memS t1
    obtain ⟨_, a2, z2, l2, m2⟩ := memS t2
    obtain ⟨⟨k1, z₁, a₁⟩, p1⟩ := t1
    obtain ⟨⟨k2, z₂, a₂⟩, p2⟩ := t2
    dsimp only at h' a1 z1 l1 m1 a2 z2 l2 m2 p1
    have hk : k1 = k2 := by
      rw [← h'] at m2
      have hpos : 0 < C.length / k1 := by
        rcases Nat.eq_zero_or_pos (C.length / k1) with h0 | h0
        · rw [h0] at m1; omega
        · exact h0
      exact Nat.eq_of_mul_eq_mul_right hpos (m1.trans m2.symm)
    subst hk
    have hz : nf z₁ = nf z₂ := by
      obtain ⟨k', rfl⟩ : ∃ k', k1 = k' + 1 := ⟨k1 - 1, by have := p1.1; omega⟩
      rw [← take_rep_succ (nf z₁) k', ← take_rep_succ (nf z₂) k', z1, z2, l1, l2]
    have hz' : z₁ = z₂ := by rw [← wprod_nf z₁, hz, wprod_nf]
    have ha' : a₁ = a₂ := by rw [← wprod_nf a₁, a1, ← a2, wprod_nf]
    subst hz' ha'
    rfl
  · rintro ⟨ℓ, hℓ⟩
    have hℓ' := hℓ
    rw [hS, Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors] at hℓ'
    obtain ⟨hne', ⟨hd, _⟩, hpd⟩ := hℓ'
    have hℓ0 : 0 < ℓ := Nat.pos_of_dvd_of_pos hd hL
    have hrep := rep_of_pd hpd hd hℓ0
    obtain ⟨k, hk⟩ := hd
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    have hdiv : C.length / ℓ = k := by rw [hk]; exact Nat.mul_div_cancel_left _ hℓ0
    rw [hdiv] at hrep
    have hZred : Red (C.take ℓ) := by
      have : Red (C.take ℓ ++ C.drop ℓ) := by rw [List.take_append_drop]; exact red_left hCC
      exact red_left this
    have hPred : Red P := by
      have := nf_red g
      rw [hnf] at this
      exact red_left (red_left this)
    have hnfz : nf (wprod (C.take ℓ)) = C.take ℓ := nf_wprod hZred
    have hnfa : nf (wprod P) = P := nf_wprod hPred
    have hlenZ : (C.take ℓ).length = ℓ := by
      rw [List.length_take, hk]
      have : ℓ * 2 ≤ ℓ * k := Nat.mul_le_mul_left _ hk2
      omega
    refine ⟨⟨⟨k, wprod (C.take ℓ), wprod P⟩, hk2, ?_, ?_, ?_⟩, ?_⟩
    · intro h
      have h0 := nf_eq_nil_iff.2 h
      rw [hnfz] at h0
      rw [h0] at hlenZ
      simp at hlenZ
      omega
    · show g = wprod P * wprod (C.take ℓ) ^ k * (wprod P)⁻¹
      rw [← wprod_rep, hrep, ← wprod_inv, ← wprod_append, ← wprod_append, ← hnf, wprod_nf]
    · show len g = 2 * len (wprod P) + k * len (wprod (C.take ℓ))
      rw [len_eq, len_eq, len_eq, hnfz, hnfa, hnf, hlenZ]
      simp only [List.length_append, length_inv]
      rw [hk]
      ring
    · apply Subtype.ext
      show C.length / k = ℓ
      rw [hk]
      exact Nat.mul_div_cancel _ (by omega)

/-! ## The two stubs -/

theorem cfun_eq_per (a : G r s) (u : List (Lt r s)) (hne : u ≠ []) (hc : CycRed u) :
    cfun (a * wprod u * a⁻¹) = (per u : ℤ) - 1 := by
  obtain ⟨P, C, hCne, hCC, hred, hw, hrot⟩ := dec_conj hne (red_sq_of_cycRed hc) a
  generalize a * wprod u * a⁻¹ = g at hw ⊢
  have hnf : nf g = P ++ C ++ inv P := by rw [← hw]; exact nf_wprod hred
  have hnot : ¬ (g ≠ 1 ∧ g * g = 1) := by
    rintro ⟨_, h2⟩
    rw [← hw, wprod_append, wprod_append, wprod_inv] at h2
    have h3 := gid_sq_conj (H := G r s) _ _ h2
    rw [← wprod_append] at h3
    have h4 := eq_nil_of_red_of_wprod hCC h3
    simp at h4
    exact hCne h4
  have hL : 0 < C.length := List.length_pos_iff.2 hCne
  have hmem : C.length ∈ (Nat.divisors C.length).filter (Pd C) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨dvd_rfl, by omega⟩, ?_⟩
    intro t ht
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  rw [cfun_of_not hnot, card_triples hCne hCC hnf, ← per_rot hrot, per_eq,
    ← Finset.card_erase_add_one hmem]
  push_cast
  ring

theorem cfun_torsion (a : G r s) (j : Fin s) :
    cfun (a * genL (Sum.inr j) * a⁻¹) = -1 := by
  have hmm : genL (Sum.inr j : Lt r s) * genL (Sum.inr j) = 1 := by
    have h := genL_bar (r := r) (s := s) (Sum.inr j)
    have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
    rw [hb] at h
    exact (mul_eq_one_iff_eq_inv (G := G r s)).2 h
  have hm1 : genL (Sum.inr j : Lt r s) ≠ 1 := by
    intro h
    have h1 := nf_wprod (r := r) (s := s) (u := [Sum.inr j]) (List.isChain_singleton _)
    rw [wprod_singleton, h, nf_one] at h1
    simp at h1
  have hg1 : a * genL (Sum.inr j) * a⁻¹ ≠ 1 := fun h =>
    hm1 (gid_conj_eq_one (H := G r s) _ _ h)
  have hgg : a * genL (Sum.inr j) * a⁻¹ * (a * genL (Sum.inr j) * a⁻¹) = 1 :=
    gid_conj_sq (H := G r s) _ _ hmm
  generalize a * genL (Sum.inr j) * a⁻¹ = g at hg1 hgg ⊢
  have hempty : IsEmpty (Tr g) := ⟨by
    rintro ⟨⟨k, z, a'⟩, hk, hz, hg, hl⟩
    dsimp only at hk hz hg hl
    have h2 := red_sq_of_triple hk hg hl
    have hZ : nf z ≠ [] := fun h => hz (nf_eq_nil_iff.1 h)
    rw [hg] at hgg
    have h3 : z ^ (k + k) = 1 := gid_conj_pow_sq (H := G r s) a' z k hgg
    have h4 := wprod_pow_ne_one h2 hZ (k := k + k) (by omega)
    rw [wprod_nf] at h4
    exact h4 h3⟩
  rw [cfun_of_inv ⟨hg1, hgg⟩, Nat.card_of_isEmpty]
  simp

end BordenaveCollins.PartF2

end
end

section
/-!
# The statements proved in Part F2, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem cfun_eq_per (a : G r s) (u : List (Lt r s)) (hne : u ≠ []) (hc : CycRed u) :
    cfun (a * wprod u * a⁻¹) = (per u : ℤ) - 1 :=
  PartF2.cfun_eq_per a u hne hc

theorem cfun_torsion (a : G r s) (j : Fin s) :
    cfun (a * genL (Sum.inr j) * a⁻¹) = -1 :=
  PartF2.cfun_torsion a j

end BordenaveCollins

end
end

section
/-!
# Part C, counting: permutations extending a partial injection, perfect matchings containing
a partial matching
-/

open Finset
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartC

/-! ## Permutations extending a partial injection -/

section Count

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma card_stab (A : Finset α) :
    (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      (Fintype.card α - A.card).factorial := by
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : α => a ∉ A)
  have h1 : (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      Fintype.card { f : Equiv.Perm α // ∀ a, ¬ (a ∉ A) → f a = a } := by
    rw [Fintype.card_subtype]; congr 1; ext π; simp
  rw [h1, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype]
  congr 1
  rw [← Finset.card_compl]
  congr 1
  ext a; simp

lemma exists_ext (E : Finset (α × α)) (h : PInj E) :
    ∃ τ : Equiv.Perm α, ∀ p ∈ E, τ p.1 = p.2 := by
  have key : ∀ a ∈ E.image Prod.fst, ∃ p ∈ E, p.1 = a := by
    intro a ha; simpa using ha
  let f : {a // a ∈ E.image Prod.fst} → {b // b ∈ E.image Prod.snd} := fun a =>
    ⟨(Classical.choose (key a.1 a.2)).2,
      mem_image_of_mem _ (Classical.choose_spec (key a.1 a.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 := Classical.choose_spec (key a.1 a.2)
      have h2 := Classical.choose_spec (key a'.1 a'.2)
      have : (Classical.choose (key a.1 a.2)).2 = (Classical.choose (key a'.1 a'.2)).2 :=
        congrArg Subtype.val haa
      apply Subtype.ext
      rw [← h1.2, ← h2.2]
      exact (h _ h1.1 _ h2.1).2 this
    · intro b
      obtain ⟨q, hq, hqb⟩ := mem_image.1 b.2
      refine ⟨⟨q.1, mem_image_of_mem _ hq⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec (key q.1 (mem_image_of_mem _ hq))
      show (Classical.choose (key q.1 (mem_image_of_mem _ hq))).2 = b.1
      rw [← hqb]
      exact (h _ h1.1 _ hq).1 h1.2
  refine ⟨(Equiv.ofBijective f hf).extendSubtype, fun p hp => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ _ (mem_image_of_mem _ hp)]
  have h1 := Classical.choose_spec (key p.1 (mem_image_of_mem _ hp))
  exact (h _ h1.1 _ hp).1 h1.2

lemma card_ext_pos (E : Finset (α × α)) (h : PInj E) :
    (univ.filter fun τ : Equiv.Perm α => ∀ p ∈ E, τ p.1 = p.2).card =
      (Fintype.card α - E.card).factorial := by
  obtain ⟨τ₀, hτ₀⟩ := exists_ext E h
  have hA : (E.image Prod.fst).card = E.card :=
    card_image_of_injOn (fun p hp q hq hpq => Prod.ext hpq ((h p hp q hq).1 hpq))
  rw [← hA, ← card_stab]
  refine card_nbij' (fun τ => τ₀⁻¹ * τ) (fun π => τ₀ * π) ?_ ?_ ?_ ?_
  · intro τ hτ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
    intro a ha
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ E, p.1 = a := by simpa using ha
    rw [Equiv.Perm.mul_apply, hτ p hp, ← hτ₀ p hp]
    simp
  · intro π hπ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    intro p hp
    rw [Equiv.Perm.mul_apply, hπ p.1 (mem_image_of_mem _ hp), hτ₀ p hp]
  · intro τ _; simp
  · intro π _; simp

lemma card_ext_neg (E : Finset (α × α)) (h : ¬ PInj E) :
    (univ.filter fun τ : Equiv.Perm α => ∀ p ∈ E, τ p.1 = p.2).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro τ _ hτ
  apply h
  intro p hp q hq
  constructor
  · intro e; rw [← hτ p hp, ← hτ q hq, e]
  · intro e; apply τ.injective; rw [hτ p hp, hτ q hq, e]

end Count

/-! ## Perfect matchings containing a partial matching -/

section Match

variable {N : ℕ}

/-- The matching `σ` contains the pairs of `E`. -/
def Cont (E : Finset (Sym2 (Fin N))) (σ : DerandSq.PM N) : Prop :=
  ∀ a b, s(a, b) ∈ E → σ.1 a = b

/-- The number of perfect matchings containing `E`. -/
def cnt (E : Finset (Sym2 (Fin N))) : ℕ :=
  (univ.filter fun σ : DerandSq.PM N => Cont E σ).card

/-- The points covered by `E`. -/
def supp (E : Finset (Sym2 (Fin N))) : Finset (Fin N) :=
  univ.filter fun x => ∃ y, s(x, y) ∈ E

lemma mem_supp (E : Finset (Sym2 (Fin N))) (x : Fin N) : x ∈ supp E ↔ ∃ y, s(x, y) ∈ E := by
  simp [supp]

lemma cont_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (σ : DerandSq.PM N) :
    Cont (insert s(a, b) E) σ ↔ σ.1 a = b ∧ Cont E σ := by
  constructor
  · intro h
    exact ⟨h a b (mem_insert_self _ _), fun x y hxy => h x y (mem_insert_of_mem hxy)⟩
  · rintro ⟨hab, h⟩ x y hxy
    rcases mem_insert.1 hxy with e | e
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · rw [← hab]; exact (σ.2 y).1
    · exact h x y e

lemma cnt_eq_sum (E : Finset (Sym2 (Fin N))) (a : Fin N) :
    cnt E = ∑ b, cnt (insert s(a, b) E) := by
  unfold cnt
  rw [card_eq_sum_card_fiberwise (f := fun σ : DerandSq.PM N => σ.1 a) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, cont_insert]
  tauto

/-- Conjugation of a perfect matching by a permutation. -/
def conjPM (π : Equiv.Perm (Fin N)) (σ : DerandSq.PM N) : DerandSq.PM N :=
  ⟨π * σ.1 * π⁻¹, fun x => by
    refine ⟨?_, ?_⟩
    · have h1 := fun y => (σ.2 y).1
      simp [h1]
    · simp only [Equiv.Perm.mul_apply]
      intro h
      apply (σ.2 (π⁻¹ x)).2
      have := congrArg (fun y => π⁻¹ y) h
      simpa using this⟩

lemma conjPM_apply (π : Equiv.Perm (Fin N)) (σ : DerandSq.PM N) (x : Fin N) :
    (conjPM π σ).1 x = π (σ.1 (π⁻¹ x)) := rfl

lemma conjPM_conjPM (π : Equiv.Perm (Fin N)) (hπ : π⁻¹ = π) (σ : DerandSq.PM N) :
    conjPM π (conjPM π σ) = σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [conjPM_apply, conjPM_apply]
  have h1 : ∀ y, π (π y) = y := fun y =>
    calc π (π y) = π⁻¹ (π y) := by rw [hπ]
      _ = y := by simp
  rw [hπ, h1, h1]

lemma cont_conj (E : Finset (Sym2 (Fin N))) (a b b' : Fin N) (hb : b ≠ a) (hb' : b' ≠ a)
    (hbE : b ∉ supp E) (hbE' : b' ∉ supp E) (σ : DerandSq.PM N)
    (h : Cont (insert s(a, b) E) σ) :
    Cont (insert s(a, b') E) (conjPM (Equiv.swap b b') σ) := by
  rw [cont_insert] at h ⊢
  rw [mem_supp] at hbE hbE'
  push Not at hbE hbE'
  refine ⟨?_, ?_⟩
  · rw [conjPM_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hb.symm hb'.symm, h.1]
    simp
  · intro x y hxy
    have hx1 : x ≠ b := by rintro rfl; exact hbE y hxy
    have hx2 : x ≠ b' := by rintro rfl; exact hbE' y hxy
    have hxy' : s(y, x) ∈ E := by rw [Sym2.eq_swap]; exact hxy
    have hy1 : y ≠ b := by rintro rfl; exact hbE x hxy'
    have hy2 : y ≠ b' := by rintro rfl; exact hbE' x hxy'
    rw [conjPM_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hx1 hx2, h.2 x y hxy,
      Equiv.swap_apply_of_ne_of_ne hy1 hy2]

lemma cnt_swap (E : Finset (Sym2 (Fin N))) (a b b' : Fin N) (hb : b ≠ a) (hb' : b' ≠ a)
    (hbE : b ∉ supp E) (hbE' : b' ∉ supp E) :
    cnt (insert s(a, b) E) = cnt (insert s(a, b') E) := by
  unfold cnt
  refine card_nbij' (conjPM (Equiv.swap b b')) (conjPM (Equiv.swap b b')) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    exact cont_conj E a b b' hb hb' hbE hbE' σ hσ
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    have := cont_conj E a b' b hb' hb hbE' hbE σ hσ
    rwa [Equiv.swap_comm] at this
  · intro σ _; exact conjPM_conjPM _ (Equiv.swap_inv _ _) σ
  · intro σ _; exact conjPM_conjPM _ (Equiv.swap_inv _ _) σ

lemma cnt_bad (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E)
    (hb : b = a ∨ b ∈ supp E) : cnt (insert s(a, b) E) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro σ _ h
  rw [cont_insert] at h
  rcases hb with rfl | hb
  · exact (σ.2 b).2 h.1
  · obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
    have h1 : σ.1 b = y := h.2 b y hy
    have h2 : σ.1 b = a := by rw [← h.1]; exact (σ.2 a).1
    apply ha
    rw [mem_supp]
    refine ⟨b, ?_⟩
    rw [Sym2.eq_swap, ← h2, h1]; exact hy

lemma supp_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) :
    supp (insert s(a, b) E) = insert a (insert b (supp E)) := by
  ext x
  simp only [mem_supp, mem_insert]
  constructor
  · rintro ⟨y, e | e⟩
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨y, e⟩)
  · rintro (rfl | rfl | ⟨y, hy⟩)
    · exact ⟨b, Or.inl rfl⟩
    · exact ⟨a, Or.inl Sym2.eq_swap⟩
    · exact ⟨y, Or.inr hy⟩

lemma pmat_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (h : PMat (insert s(a, b) E))
    (hn : s(a, b) ∉ E) : PMat E ∧ a ≠ b ∧ a ∉ supp E ∧ b ∉ supp E := by
  refine ⟨⟨fun p hp => h.1 p (mem_insert_of_mem hp), fun p hp q hq =>
    h.2 p (mem_insert_of_mem hp) q (mem_insert_of_mem hq)⟩, ?_, ?_, ?_⟩
  · intro e
    exact h.1 _ (mem_insert_self _ _) (Sym2.mk_isDiag_iff.2 e)
  · intro ha
    obtain ⟨y, hy⟩ := (mem_supp E a).1 ha
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨a, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)
  · intro hb
    obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨b, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)

lemma card_supp (E : Finset (Sym2 (Fin N))) : PMat E → (supp E).card = 2 * E.card := by
  induction E using Finset.induction_on with
  | empty => intro _; simp [supp]
  | insert p E hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert E a b h hp
      rw [supp_insert, card_insert_of_notMem, card_insert_of_notMem hb, ih hE,
        card_insert_of_notMem hp]
      · ring
      · simp [hab, ha]

lemma two_mul_card_le (E : Finset (Sym2 (Fin N))) (h : PMat E) : 2 * E.card ≤ N := by
  rw [← card_supp E h]
  exact (card_le_univ _).trans (Fintype.card_fin N).le

lemma cnt_mul (E : Finset (Sym2 (Fin N))) :
    PMat E → cnt E * ∏ l ∈ range E.card, (N - 2 * l - 1) = Fintype.card (DerandSq.PM N) := by
  induction E using Finset.induction_on with
  | empty =>
    intro _
    simp [cnt, Cont]
  | insert p E hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert E a b h hp
      have hV : cnt E = (N - 2 * E.card - 1) * cnt (insert s(a, b) E) := by
        rw [cnt_eq_sum E a, ← sum_subset (subset_univ (univ \ insert a (supp E)))]
        · rw [sum_congr rfl (g := fun _ => cnt (insert s(a, b) E)), sum_const, smul_eq_mul]
          · congr 1
            rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
              card_insert_of_notMem ha, card_supp E hE]
            omega
          · intro b' hb'
            simp only [mem_sdiff, mem_univ, true_and, mem_insert, not_or] at hb'
            exact cnt_swap E a b' b hb'.1 (Ne.symm hab) hb'.2 hb
        · intro b' _ hb'
          simp only [mem_sdiff, mem_univ, true_and, mem_insert, not_not] at hb'
          exact cnt_bad E a b' ha hb'
      rw [card_insert_of_notMem hp, prod_range_succ, ← ih hE, hV]
      ring

lemma cnt_not_pmat (E : Finset (Sym2 (Fin N))) (h : ¬ PMat E) : cnt E = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro σ _ hσ
  apply h
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · induction p using Sym2.inductionOn with
    | hf a b =>
      rw [Sym2.mk_isDiag_iff]
      intro e
      have := hσ a b hp
      rw [← e] at this
      exact (σ.2 a).2 this
  · induction p using Sym2.inductionOn with
    | hf a b =>
      induction q using Sym2.inductionOn with
      | hf a' b' =>
        rintro ⟨x, hx, hx'⟩
        have h1 := hσ a b hp
        have h2 := hσ a' b' hq
        have h3 : σ.1 b = a := by rw [← h1]; exact (σ.2 a).1
        have h4 : σ.1 b' = a' := by rw [← h2]; exact (σ.2 a').1
        rw [Sym2.eq_iff]
        rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rcases Sym2.mem_iff.1 hx' with rfl | rfl
        · exact Or.inl ⟨rfl, h1.symm.trans h2⟩
        · exact Or.inr ⟨rfl, h1.symm.trans h4⟩
        · exact Or.inr ⟨h3.symm.trans h2, rfl⟩
        · exact Or.inl ⟨h3.symm.trans h4, rfl⟩

lemma prod_cast (k : ℕ) (hk : 2 * k ≤ N) :
    ((∏ l ∈ range k, (N - 2 * l - 1) : ℕ) : ℝ) = ∏ l ∈ range k, ((N : ℝ) - 2 * l - 1) := by
  rw [Nat.cast_prod]
  refine prod_congr rfl fun l hl => ?_
  have := mem_range.1 hl
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

lemma prod_ne_zero' (k : ℕ) (hk : 2 * k ≤ N) :
    ∏ l ∈ range k, ((N : ℝ) - 2 * l - 1) ≠ 0 := by
  rw [← prod_cast k hk, Nat.cast_ne_zero, prod_ne_zero_iff]
  intro l hl
  have := mem_range.1 hl
  omega

lemma cnt_real (E : Finset (Sym2 (Fin N))) (h : PMat E) :
    (cnt E : ℝ) = (Fintype.card (DerandSq.PM N) : ℝ) /
      ∏ l ∈ range E.card, ((N : ℝ) - 2 * l - 1) := by
  have h2 := two_mul_card_le E h
  rw [eq_div_iff (prod_ne_zero' _ h2), ← prod_cast _ h2, ← Nat.cast_mul, cnt_mul E h]

lemma card_PM_ne_zero (hN : Even N) : Fintype.card (DerandSq.PM N) ≠ 0 := by
  obtain ⟨n, rfl⟩ := hN
  rw [← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
  refine ⟨⟨finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv), fun x => ?_⟩⟩
  refine ⟨?_, ?_⟩
  · simp
  · intro h
    have h' : (Equiv.sumComm (Fin n) (Fin n)) (finSumFinEquiv.symm x) = finSumFinEquiv.symm x := by
      apply finSumFinEquiv.injective
      simpa using h
    rcases hx : finSumFinEquiv.symm x with y | y <;> rw [hx] at h' <;> simp at h'

end Match

end BordenaveCollins.PartC
end
end

section
/-!
# Part C, paths: the counting formula for the expected number of fixed points of a word
-/

open Finset
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartC

/-! ## Paths along a word -/

section Word

variable {r s : ℕ} (u : List (Lt r s))

/-- `ω` realises the path `x`. -/
def Rz {N : ℕ} (ω : Om r s N) (x : Fin (u.length + 1) → Fin N) : Prop :=
  ∀ t : Fin u.length, x t.castSucc = letterPerm ω (u.get t) (x t.succ)

/-- The path of `y` under `ω`. -/
def path {N : ℕ} (ω : Om r s N) (y : Fin N) : Fin (u.length + 1) → Fin N :=
  fun t => wordPerm ω (u.drop t) y

lemma wordPerm_cons_apply {N : ℕ} (ω : Om r s N) (l : Lt r s) (ws : List (Lt r s))
    (y : Fin N) : wordPerm ω (l :: ws) y = letterPerm ω l (wordPerm ω ws y) := by
  simp [wordPerm, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (ω : Om r s N) (y : Fin N) : path u ω y (Fin.last _) = y := by
  simp [path, wordPerm]

lemma path_zero {N : ℕ} (ω : Om r s N) (y : Fin N) : path u ω y 0 = wordPerm ω u y := by
  simp [path]

lemma path_step {N : ℕ} (ω : Om r s N) (y : Fin N) (t : Fin u.length) :
    path u ω y t.castSucc = letterPerm ω (u.get t) (path u ω y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPerm_cons_apply]
  rfl

lemma eq_path {N : ℕ} (ω : Om r s N) (x : Fin (u.length + 1) → Fin N) (hx : Rz u ω x) :
    x = path u ω (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (ω : Om r s N) :
    fixCount (wordPerm ω u) =
      (univ.filter fun x : Fin (u.length + 1) → Fin N =>
        Rz u ω x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path u ω) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := eq_path u ω x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨fun t => path_step u ω y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    exact (eq_path u ω x hx.1).symm
  · intro y _
    exact path_last u ω y

lemma Rz_iff {N : ℕ} (ω : Om r s N) (x : Fin (u.length + 1) → Fin N) :
    Rz u ω x ↔ (∀ i, ∀ p ∈ Es u x i, ω.1 i p.1 = p.2) ∧ ∀ j, Cont (Ms u x j) (ω.2 j) := by
  constructor
  · intro h
    refine ⟨fun i p hp => ?_, fun j a b hab => ?_⟩
    · rcases mem_union.1 hp with hp | hp
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
        have ht := (mem_filter.1 ht).2
        have h' := h t
        rw [ht] at h'
        exact h'.symm
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
        have ht := (mem_filter.1 ht).2
        have h' := h t
        rw [ht] at h'
        show ω.1 i (x t.castSucc) = x t.succ
        rw [h']; simp [letterPerm]
    · obtain ⟨t, ht, e⟩ := mem_image.1 hab
      have ht := (mem_filter.1 ht).2
      have h' := h t
      rw [ht] at h'
      have h'' : x t.castSucc = (ω.2 j).1 (x t.succ) := h'
      rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h'']; exact ((ω.2 j).2 _).1
      · exact h''.symm
  · rintro ⟨h1, h2⟩ t
    rcases hl : u.get t with ⟨i, b⟩ | j
    · cases b
      · have := h1 i (x t.castSucc, x t.succ)
          (mem_union_right _ (mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩))
        simp only at this
        simp [letterPerm, ← this]
      · have := h1 i (x t.succ, x t.castSucc)
          (mem_union_left _ (mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩))
        exact this.symm
    · have := h2 j (x t.castSucc) (x t.succ)
        (mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩)
      show x t.castSucc = (ω.2 j).1 (x t.succ)
      rw [← this]; exact (((ω.2 j).2 _).1).symm

lemma card_Rz {N : ℕ} (x : Fin (u.length + 1) → Fin N) :
    (univ.filter fun ω : Om r s N => Rz u ω x).card =
      (∏ i, (univ.filter fun τ : Equiv.Perm (Fin N) => ∀ p ∈ Es u x i, τ p.1 = p.2).card) *
        ∏ j, cnt (Ms u x j) := by
  have : (univ.filter fun ω : Om r s N => Rz u ω x) =
      (Fintype.piFinset fun i => univ.filter fun τ : Equiv.Perm (Fin N) =>
        ∀ p ∈ Es u x i, τ p.1 = p.2) ×ˢ
      (Fintype.piFinset fun j => univ.filter fun σ : DerandSq.PM N => Cont (Ms u x j) σ) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_product, Fintype.mem_piFinset]
    exact Rz_iff u ω x
  rw [this, card_product, Fintype.card_piFinset, Fintype.card_piFinset]
  rfl

/-- The weight of a path: the number of samples realising it. -/
def W (N : ℕ) {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) : ℝ :=
  if Good u x then (∏ i, ((N - (Es u x i).card).factorial : ℝ)) *
    ∏ j, ((Fintype.card (DerandSq.PM N) : ℝ) /
      ∏ l ∈ range (Ms u x j).card, ((N : ℝ) - 2 * l - 1)) else 0

lemma sum_fixCount (N : ℕ) :
    (∑ ω : Om r s N, (fixCount (wordPerm ω u) : ℝ)) =
      ∑ x : Fin (u.length + 1) → Fin N, W u N x := by
  have h0 : ∀ ω : Om r s N, (fixCount (wordPerm ω u) : ℝ) =
      ∑ x : Fin (u.length + 1) → Fin N,
        if Rz u ω x ∧ x 0 = x (Fin.last _) then (1 : ℝ) else 0 := by
    intro ω; rw [fixCount_eq, Finset.sum_boole]
  simp only [h0]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  by_cases hcl : x 0 = x (Fin.last _)
  · have h1 : (∑ ω : Om r s N, if Rz u ω x ∧ x 0 = x (Fin.last _) then (1 : ℝ) else 0) =
        ((univ.filter fun ω : Om r s N => Rz u ω x).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine sum_congr rfl fun ω _ => ?_
      simp only [hcl, and_true]
    rw [h1, card_Rz]
    push_cast
    by_cases hg : Good u x
    · unfold W
      rw [if_pos hg]
      congr 1
      · refine prod_congr rfl fun i _ => ?_
        rw [card_ext_pos _ (hg.1 i), Fintype.card_fin]
      · refine prod_congr rfl fun j _ => ?_
        rw [cnt_real _ (hg.2.1 j)]
    · unfold W
      rw [if_neg hg]
      by_cases h1 : ∀ i, PInj (Es u x i)
      · by_cases h2 : ∀ j, PMat (Ms u x j)
        · exact absurd ⟨h1, h2, hcl⟩ hg
        · push Not at h2
          obtain ⟨j, hj⟩ := h2
          rw [mul_eq_zero]; right
          refine prod_eq_zero (mem_univ j) ?_
          rw [cnt_not_pmat _ hj]; simp
      · push Not at h1
        obtain ⟨i, hi⟩ := h1
        rw [mul_eq_zero]; left
        refine prod_eq_zero (mem_univ i) ?_
        rw [card_ext_neg _ hi]; simp
  · unfold W
    rw [if_neg (fun h => hcl h.2.2)]
    simp [hcl]

end Word

/-! ## Canonical representatives of kernels -/

section Canon

variable {n : ℕ} {α : Type*} [DecidableEq α]

lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end Canon

/-! ## Invariance under relabelling -/

section Invariance

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
lemma sym2_map_inj (φ : β → α) (S : Set β) (hφ : Set.InjOn φ S) (p q : Sym2 β)
    (hp : ∀ a ∈ p, a ∈ S) (hq : ∀ a ∈ q, a ∈ S) (h : Sym2.map φ p = Sym2.map φ q) : p = q := by
  induction p using Sym2.inductionOn with
  | hf a b =>
    induction q using Sym2.inductionOn with
    | hf a' b' =>
      have ha := hp a (Sym2.mem_mk_left _ _)
      have hb := hp b (Sym2.mem_mk_right _ _)
      have ha' := hq a' (Sym2.mem_mk_left _ _)
      have hb' := hq b' (Sym2.mem_mk_right _ _)
      rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at h
      rw [Sym2.eq_iff]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hφ ha ha' h1, hφ hb hb' h2⟩
      · exact Or.inr ⟨hφ ha hb' h1, hφ hb ha' h2⟩

omit [DecidableEq β] in
lemma pmat_image (E : Finset (Sym2 β)) (φ : β → α) (S : Set β) (hφ : Set.InjOn φ S)
    (hE : ∀ p ∈ E, ∀ a ∈ p, a ∈ S) : PMat (E.image (Sym2.map φ)) ↔ PMat E := by
  unfold PMat
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine and_congr (forall₂_congr fun p hp => ?_)
    (forall₂_congr fun p hp => forall₂_congr fun q hq => ?_)
  · have := hE p hp
    induction p using Sym2.inductionOn with
    | hf a b =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff, Sym2.mk_isDiag_iff,
        hφ.eq_iff (this a (Sym2.mem_mk_left _ _)) (this b (Sym2.mem_mk_right _ _))]
  · constructor
    · intro H y hy hy'
      exact sym2_map_inj φ S hφ p q (hE p hp) (hE q hq)
        (H (φ y) (Sym2.mem_map.2 ⟨y, hy, rfl⟩) (Sym2.mem_map.2 ⟨y, hy', rfl⟩))
    · intro H x hx hx'
      obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.1 hx
      obtain ⟨y', hy', e⟩ := Sym2.mem_map.1 hx'
      have : y' = y := hφ (hE q hq y' hy') (hE p hp y hy) e
      subst this
      rw [H _ hy hy']

omit [DecidableEq β] in
lemma pinj_image (E : Finset (β × β)) (φ : β → α) (S : Set β) (hφ : Set.InjOn φ S)
    (hE : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S) : PInj (E.image (Prod.map φ φ)) ↔ PInj E := by
  unfold PInj
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.map_fst,
    Prod.map_snd]
  refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
  have hp' := hE p hp
  have hq' := hE q hq
  rw [hφ.eq_iff hp'.1 hq'.1, hφ.eq_iff hp'.2 hq'.2]

variable {r s : ℕ} (u : List (Lt r s))

lemma Es_comp (c : Fin (u.length + 1) → β) (φ : β → α) (i : Fin r) :
    Es u (φ ∘ c) i = (Es u c i).image (Prod.map φ φ) := by
  simp only [Es, image_union, image_image]
  rfl

lemma Ms_comp (c : Fin (u.length + 1) → β) (φ : β → α) (j : Fin s) :
    Ms u (φ ∘ c) j = (Ms u c j).image (Sym2.map φ) := by
  simp only [Ms, image_image]
  rfl

lemma Es_range (c : Fin (u.length + 1) → β) (i : Fin r) (p : β × β) (hp : p ∈ Es u c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  rcases mem_union.1 hp with hp | hp <;> obtain ⟨t, -, rfl⟩ := mem_image.1 hp <;>
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

lemma Ms_range (c : Fin (u.length + 1) → β) (j : Fin s) (p : Sym2 β) (hp : p ∈ Ms u c j) :
    ∀ a ∈ p, a ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  intro a ha
  rcases Sym2.mem_iff.1 ha with rfl | rfl <;> exact ⟨_, rfl⟩

variable (c : Fin (u.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

lemma card_Es_comp (i : Fin r) : (Es u (φ ∘ c) i).card = (Es u c i).card := by
  rw [Es_comp]
  refine card_image_of_injOn fun p hp q hq hpq => ?_
  have hp' := Es_range u c i p hp
  have hq' := Es_range u c i q hq
  simp only [Prod.map, Prod.mk.injEq] at hpq
  exact Prod.ext (hφ hp'.1 hq'.1 hpq.1) (hφ hp'.2 hq'.2 hpq.2)

lemma card_Ms_comp (j : Fin s) : (Ms u (φ ∘ c) j).card = (Ms u c j).card := by
  rw [Ms_comp]
  exact card_image_of_injOn fun p hp q hq hpq =>
    sym2_map_inj φ _ hφ p q (Ms_range u c j p hp) (Ms_range u c j q hq) hpq

lemma good_comp : Good u (φ ∘ c) ↔ Good u c := by
  unfold Good
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun j => ?_) ?_)
  · rw [Es_comp]
    exact pinj_image _ φ _ hφ (Es_range u c i)
  · rw [Ms_comp]
    exact pmat_image _ φ _ hφ (Ms_range u c j)
  · exact hφ.eq_iff ⟨_, rfl⟩ ⟨_, rfl⟩

lemma W_comp (N : ℕ) : W u N (φ ∘ c) = W u N c := by
  unfold W
  simp only [good_comp u c φ hφ, card_Es_comp u c φ hφ, card_Ms_comp u c φ hφ]

end Invariance

/-! ## Bounds on the invariants -/

section Bounds

variable {r s : ℕ} (u : List (Lt r s)) {α : Type*} [DecidableEq α]

/-- The number of edges of a path is at most the length of the word. -/
lemma sum_card_le (x : Fin (u.length + 1) → α) :
    ∑ i, (Es u x i).card + ∑ j, (Ms u x j).card ≤ u.length := by
  let F : Lt r s → Finset (Fin u.length) := fun a => univ.filter fun t => u.get t = a
  calc ∑ i, (Es u x i).card + ∑ j, (Ms u x j).card
      ≤ ∑ i, ((F (Sum.inl (i, true))).card + (F (Sum.inl (i, false))).card) +
          ∑ j, (F (Sum.inr j)).card :=
        add_le_add
          (sum_le_sum fun i _ => (card_union_le _ _).trans (add_le_add card_image_le card_image_le))
          (sum_le_sum fun j _ => card_image_le)
    _ = ∑ a : Lt r s, (F a).card := by
        rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool]
    _ = (univ : Finset (Fin u.length)).card :=
        (card_eq_sum_card_fiberwise (f := u.get) (s := univ) (t := univ)
          (fun _ _ => mem_univ _)).symm
    _ = u.length := by rw [card_univ, Fintype.card_fin]

lemma card_Es_le (x : Fin (u.length + 1) → α) (i : Fin r) : (Es u x i).card ≤ u.length :=
  le_trans (le_trans (single_le_sum (f := fun i => (Es u x i).card) (fun _ _ => Nat.zero_le _)
    (mem_univ i)) (Nat.le_add_right _ _)) (sum_card_le u x)

end Bounds

/-! ## The counting formula -/

theorem expect_formula_aux {r s : ℕ} (u : List (Lt r s)) (N : ℕ) (hA : Adm s N)
    (hL : u.length ≤ N) :
    expFixW r s N u =
      ∑ c ∈ (univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) =>
        canon c = c).filter (Good u), wt u N c := by
  have h1 : (∑ ω : Om r s N, (fixCount (wordPerm ω u) : ℝ)) =
      ∑ c ∈ (univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c),
        (N.descFactorial (nv c) : ℝ) * W u N c := by
    rw [sum_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
      (t := univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c)
      (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
    refine sum_congr rfl fun c hc => ?_
    have hc := (mem_filter.1 hc).2
    have hG : ∀ x ∈ univ.filter fun x : Fin (u.length + 1) → Fin N => canon x = c,
        W u N x = W u N c := by
      intro x hx
      have hx := (mem_filter.1 hx).2
      rw [← hx]
      conv_lhs => rw [← comp_canon x]
      exact W_comp u (canon x) x (injOn_canon x) N
    rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, nsmul_eq_mul]
  have hP : ((Fintype.card (DerandSq.PM N) : ℝ)) ^ s ≠ 0 := by
    rcases hA with h0 | hE
    · subst h0; simp
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (card_PM_ne_zero hE))
  have hcard : (Fintype.card (Om r s N) : ℝ) =
      (N.factorial : ℝ) ^ r * ((Fintype.card (DerandSq.PM N) : ℝ)) ^ s := by
    simp [Fintype.card_perm]
  unfold expFixW
  rw [h1, sum_filter (Good u), sum_div, hcard]
  refine sum_congr rfl fun c _ => ?_
  by_cases hg : Good u c
  · rw [if_pos hg]
    unfold W wt
    rw [if_pos hg]
    have he : ∀ i, (Es u c i).card ≤ N := fun i => (card_Es_le u c i).trans hL
    have hfac : (N.factorial : ℝ) ^ r =
        (∏ i, (N.descFactorial (Es u c i).card : ℝ)) *
          ∏ i, ((N - (Es u c i).card).factorial : ℝ) := by
      rw [← prod_mul_distrib,
        show (N.factorial : ℝ) ^ r = ∏ _i : Fin r, (N.factorial : ℝ) by simp]
      refine prod_congr rfl fun i _ => ?_
      rw [← Nat.cast_mul, mul_comm, Nat.factorial_mul_descFactorial (he i)]
    have hB : (∏ i, ((N - (Es u c i).card).factorial : ℝ)) ≠ 0 :=
      prod_ne_zero_iff.2 fun i _ => by positivity
    have hM : (∏ j, ((Fintype.card (DerandSq.PM N) : ℝ) /
        ∏ l ∈ range (Ms u c j).card, ((N : ℝ) - 2 * l - 1))) =
        ((Fintype.card (DerandSq.PM N) : ℝ)) ^ s /
          ∏ j, ∏ l ∈ range (Ms u c j).card, ((N : ℝ) - 2 * l - 1) := by
      rw [prod_div_distrib]; simp
    rw [hfac, hM]
    set A := (N.descFactorial (nv c) : ℝ)
    set B := ∏ i, ((N - (Es u c i).card).factorial : ℝ)
    set D := ∏ i, (N.descFactorial (Es u c i).card : ℝ)
    set M := ∏ j, ∏ l ∈ range (Ms u c j).card, ((N : ℝ) - 2 * l - 1)
    set P := ((Fintype.card (DerandSq.PM N) : ℝ)) ^ s
    calc A * (B * (P / M)) / (D * B * P) = (A * (B * P)) / ((D * M) * (B * P)) := by ring
      _ = A / (D * M) := mul_div_mul_right _ _ (mul_ne_zero hB hP)
  · rw [if_neg hg]
    unfold W
    rw [if_neg hg]
    simp

end BordenaveCollins.PartC
end
end

section
/-!
# Part C: the counting formula and rationality

Proofs of `BordenaveCollins.expect_formula` and `BordenaveCollins.rational`.
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartC

variable {r s : ℕ}

theorem expect_formula (u : List (Lt r s)) (N : ℕ) (hN : 1 ≤ N) (hA : Adm s N)
    (hL : u.length ≤ N) :
    expFixW r s N u = ∑ c ∈ CG u, wt u N c := by
  rw [expect_formula_aux u N hA hL]
  refine sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [CG, mem_filter]

/-! ## General facts on colourings -/

/-! ## The polynomials -/

/-! ## The polynomial of a colouring -/

/-! ## Rationality -/

end BordenaveCollins.PartC
end
end

section
/-!
# The statements proved in Part C, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem expect_formula (u : List (Lt r s)) (N : ℕ) (hN : 1 ≤ N) (hA : Adm s N)
    (hL : u.length ≤ N) :
    expFixW r s N u = ∑ c ∈ CG u, wt u N c :=
  PartC.expect_formula u N hN hA hL

end BordenaveCollins

end
end

section
/-!
# Part M: first-order asymptotics of the expected number of fixed points (assembly)

`tendsto_expFix` from `exists_cyc_rep`, `cfun_eq_per`, `cfun_torsion`, `act_wprod`,
`expect_formula`, `nv_le_Ecount`, `card_eq_per`.
-/

open Finset Filter Topology
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartM

/- `stp_pos` and `adm` are copies of the lemmas of the same names in `PartU` (which is built after
this module in the assembled tree). -/
theorem stp_pos (s : ℕ) : 1 ≤ stp s := by
  unfold stp; split_ifs <;> norm_num

theorem adm (s n : ℕ) : Adm s (stp s * n) := by
  unfold Adm stp
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr (even_two_mul n)

variable {r s : ℕ}

/-! ## Limits of the weights -/

/-- `N^{(m)} / N^m → 1`. -/
lemma tendsto_descFactorial_div_pow (m : ℕ) :
    Tendsto (fun N : ℕ => (N.descFactorial m : ℝ) / (N : ℝ) ^ m) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => ∏ j ∈ range m, (1 - (j : ℝ) / N)) atTop
      (𝓝 (∏ j ∈ range m, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun j _ =>
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
  simp only [sub_zero, prod_const_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max m 1)] with N hN
  have hNm : m ≤ N := le_of_max_le_left hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 1 ≤ N := le_of_max_le_right hN
    exact_mod_cast (show N ≠ 0 by omega)
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    show (N : ℝ) ^ m = ∏ _j ∈ range m, (N : ℝ) by simp, ← prod_div_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj : j < m := mem_range.1 hj
  rw [Nat.cast_sub (by omega), sub_div, div_self hN0]

/-- `∏_{l<m} (N - 2l - 1) / N^m → 1`. -/
lemma tendsto_odd_div_pow (m : ℕ) :
    Tendsto (fun N : ℕ => (∏ l ∈ range m, ((N : ℝ) - 2 * l - 1)) / (N : ℝ) ^ m) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => ∏ l ∈ range m, (1 - (2 * (l : ℝ) + 1) / N)) atTop
      (𝓝 (∏ l ∈ range m, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun l _ =>
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (2 * (l : ℝ) + 1))
  simp only [sub_zero, prod_const_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show (N : ℝ) ^ m = ∏ _j ∈ range m, (N : ℝ) by simp, ← prod_div_distrib]
  refine prod_congr rfl fun l _ => ?_
  field_simp
  ring

/-- `N^a / N^b → [a = b]` for `a ≤ b`. -/
lemma tendsto_pow_div_pow (a b : ℕ) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a / (N : ℝ) ^ b) atTop (𝓝 (if a = b then 1 else 0)) := by
  split_ifs with h
  · subst h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [div_self (pow_ne_zero _ hN0)]
  · have h1 : Tendsto (fun N : ℕ => ((N : ℝ) ^ (b - a))⁻¹) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by omega : b - a ≠ 0)).comp
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [pow_sub₀ _ hN0 hab]
    field_simp

lemma tendsto_term {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ℕ) (b : ι → ℕ) (m : κ → ℕ)
    (hab : a ≤ ∑ i, b i + ∑ j, m j) :
    Tendsto (fun N : ℕ => (N.descFactorial a : ℝ) /
        ((∏ i, (N.descFactorial (b i) : ℝ)) * ∏ j, ∏ l ∈ range (m j), ((N : ℝ) - 2 * l - 1)))
      atTop (𝓝 (if a = ∑ i, b i + ∑ j, m j then 1 else 0)) := by
  have hA := tendsto_descFactorial_div_pow a
  have hB : Tendsto (fun N : ℕ => ∏ i, (N.descFactorial (b i) : ℝ) / (N : ℝ) ^ (b i)) atTop
      (𝓝 (∏ _i : ι, (1 : ℝ))) :=
    tendsto_finsetProd _ fun i _ => tendsto_descFactorial_div_pow (b i)
  have hC : Tendsto (fun N : ℕ => ∏ j, (∏ l ∈ range (m j), ((N : ℝ) - 2 * l - 1)) /
      (N : ℝ) ^ (m j)) atTop (𝓝 (∏ _j : κ, (1 : ℝ))) :=
    tendsto_finsetProd _ fun j _ => tendsto_odd_div_pow (m j)
  rw [prod_const_one] at hB hC
  have hP := tendsto_pow_div_pow a (∑ i, b i + ∑ j, m j) hab
  have h := (hA.div (hB.mul hC) (by norm_num)).mul hP
  rw [mul_one, div_one, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Pi.div_apply]
  rw [prod_div_distrib, prod_div_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, pow_add]
  generalize (∏ i, (N.descFactorial (b i) : ℝ)) = B
  generalize (∏ j, ∏ l ∈ range (m j), ((N : ℝ) - 2 * l - 1)) = C
  generalize (N.descFactorial a : ℝ) = A
  have hx : ((N : ℝ) ^ a) ≠ 0 := pow_ne_zero _ hN0
  have hy : ((N : ℝ) ^ ∑ i, b i) ≠ 0 := pow_ne_zero _ hN0
  have hz : ((N : ℝ) ^ ∑ j, m j) ≠ 0 := pow_ne_zero _ hN0
  by_cases hB0 : B = 0
  · simp [hB0]
  by_cases hC0 : C = 0
  · simp [hC0]
  field_simp

/-! ## Fixed points -/

lemma fixCount_conj {N : ℕ} (p q : Equiv.Perm (Fin N)) :
    fixCount (p * q * p⁻¹) = fixCount q := by
  unfold fixCount
  refine (card_bij' (fun x _ => p⁻¹ x) (fun x _ => p x) ?_ ?_ ?_ ?_).trans rfl
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    have h := congrArg (fun y => p⁻¹ y) hx.2
    simpa using h
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    simp [hx.2]
  · intro x _; simp
  · intro x _; simp

lemma fixCount_act_conj {N : ℕ} (ω : Om r s N) (a : G r s) (u : List (Lt r s)) :
    fixCount (act ω (a * wprod u * a⁻¹)) = fixCount (wordPerm ω u) := by
  rw [map_mul, map_mul, PartF1.g_map_inv, PartF1.act_wprod, fixCount_conj]

lemma expFix_conj (N : ℕ) (a : G r s) (u : List (Lt r s)) :
    expFix r s N (a * wprod u * a⁻¹) = expFixW r s N u := by
  unfold expFix expFixW
  simp only [fixCount_act_conj]

lemma expFixW_torsion (N : ℕ) (j : Fin s) :
    expFixW r s N [Sum.inr j] = 0 := by
  unfold expFixW
  have h : ∀ ω : Om r s N, (fixCount (wordPerm ω [Sum.inr j]) : ℝ) = 0 := by
    intro ω
    have : fixCount (wordPerm ω [Sum.inr j]) = 0 := by
      unfold fixCount
      rw [card_eq_zero, filter_eq_empty_iff]
      intro x _
      simpa [wordPerm, letterPerm] using ((ω.2 j).2 x).2
    simp [this]
  simp [h]

/-! ## The theorem -/

theorem tendsto_expFix (g : G r s) (hg : g ≠ 1) :
    Tendsto (fun n : ℕ => expFix r s (stp s * n) g) atTop (𝓝 ((cfun g : ℝ) + 1)) := by
  obtain ⟨a, u, hne, rfl, hcase⟩ := exists_cyc_rep g hg
  simp only [expFix_conj]
  rcases hcase with hc | ⟨j, rfl⟩
  · rw [cfun_eq_per a u hne hc]
    have hT : ∀ c ∈ CG u, Tendsto (fun N : ℕ => wt u N c) atTop
        (𝓝 (if nv c = Ecount u c then 1 else 0)) := fun c hcG =>
      tendsto_term (nv c) (fun i => (Es u c i).card) (fun j => (Ms u c j).card)
        (nv_le_Ecount u hne hc c hcG)
    have hsum := tendsto_finsetSum (CG u) hT
    rw [sum_boole, card_eq_per u hne hc] at hsum
    have hst : Tendsto (fun n : ℕ => stp s * n) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (stp_pos s)) tendsto_id
    have hfin : Tendsto (fun n : ℕ => expFixW r s (stp s * n) u) atTop (𝓝 (per u : ℝ)) := by
      refine (hsum.comp hst).congr' ?_
      filter_upwards [hst.eventually (eventually_ge_atTop (max 1 u.length))] with n hn
      exact (expect_formula u _ (le_of_max_le_left hn) (adm s n)
        (le_of_max_le_right hn)).symm
    convert hfin using 2
    push_cast
    ring
  · have h1 : (wprod [Sum.inr j] : G r s) = genL (Sum.inr j) := PartF1.wprod_singleton _
    rw [h1, cfun_torsion a j]
    simp only [expFixW_torsion]
    norm_num

end BordenaveCollins.PartM

end
end

section
open Filter Topology
open BordenaveCollins

theorem solution {r s : ℕ} (g : G r s) (hg : g ≠ 1) :
    Tendsto (fun n : ℕ => expFix r s (stp s * n) g) atTop (𝓝 ((cfun g : ℝ) + 1)) :=
  BordenaveCollins.PartM.tendsto_expFix g hg

end
