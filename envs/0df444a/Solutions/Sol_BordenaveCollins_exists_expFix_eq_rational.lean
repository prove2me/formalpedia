-- Prove2me | solution 1 for BordenaveCollins.exists_expFix_eq_rational
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:20:41.31238+00:00
-- url     : https://prove2.me/submissions/46503228-11ff-4ebb-959a-9d04fadce635

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

theorem act_wprod {N : ℕ} (ω : Om r s N) (u : List (Lt r s)) :
    act ω (wprod u) = wordPerm ω u :=
  PartF1.act_wprod ω u

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

section Seq

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- The values of a sequence at positions `≤ k`. -/
def Uset (x : Fin (n + 1) → α) (k : ℕ) : Finset α :=
  (univ.filter fun t : Fin (n + 1) => t.val ≤ k).image x

/-- The (unordered) steps of a sequence before time `k`. -/
def Edset (x : Fin (n + 1) → α) (k : ℕ) : Finset (Sym2 α) :=
  (univ.filter fun t : Fin n => t.val < k).image fun t => s(x t.castSucc, x t.succ)

lemma Ed_mem_U (x : Fin (n + 1) → α) (k : ℕ) (p : Sym2 α) (hp : p ∈ Edset x k) :
    ∀ a ∈ p, a ∈ Uset x k := by
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
  have ht := (mem_filter.1 ht).2
  intro a ha
  rcases Sym2.mem_iff.1 ha with rfl | rfl
  · exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp; omega⟩)
  · exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp; omega⟩)

lemma U_Ed (x : Fin (n + 1) → α) :
    ∀ k, k ≤ n → (Uset x k).card ≤ (Edset x k).card + 1
  | 0, _ => by
      have : Uset x 0 ⊆ {x 0} := by
        intro a ha
        obtain ⟨t, ht, rfl⟩ := mem_image.1 ha
        have : t = 0 := Fin.ext (by have := (mem_filter.1 ht).2; simp only [Fin.val_zero]; omega)
        simp [this]
      calc (Uset x 0).card ≤ ({x 0} : Finset α).card := card_le_card this
        _ = 1 := card_singleton _
        _ ≤ _ := by omega
  | k + 1, hk => by
      have ih := U_Ed x k (by omega)
      let t : Fin n := ⟨k, by omega⟩
      have hU : Uset x (k + 1) ⊆ insert (x t.succ) (Uset x k) := by
        intro a ha
        obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
        have hs := (mem_filter.1 hs).2
        rcases Nat.lt_or_ge s.val (k + 1) with h | h
        · exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by omega⟩))
        · have : s = t.succ := Fin.ext (by simp [t]; omega)
          rw [this]; exact mem_insert_self _ _
      have hE : Edset x k ⊆ Edset x (k + 1) := by
        intro p hp
        obtain ⟨s, hs, rfl⟩ := mem_image.1 hp
        have hs := (mem_filter.1 hs).2
        exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by omega⟩)
      by_cases hmem : x t.succ ∈ Uset x k
      · calc (Uset x (k + 1)).card ≤ (insert (x t.succ) (Uset x k)).card := card_le_card hU
          _ = (Uset x k).card := by rw [insert_eq_of_mem hmem]
          _ ≤ (Edset x k).card + 1 := ih
          _ ≤ (Edset x (k + 1)).card + 1 := by have := card_le_card hE; omega
      · have hnew : s(x t.castSucc, x t.succ) ∉ Edset x k := fun h =>
          hmem (Ed_mem_U x k _ h _ (Sym2.mem_mk_right _ _))
        have hsub : insert s(x t.castSucc, x t.succ) (Edset x k) ⊆ Edset x (k + 1) := by
          refine insert_subset ?_ hE
          exact mem_image_of_mem (fun t : Fin n => s(x t.castSucc, x t.succ))
            (mem_filter.2 ⟨mem_univ _, by simp [t]⟩)
        have h3 := card_le_card hsub
        rw [card_insert_of_notMem hnew] at h3
        have h4 := card_le_card hU
        have h5 := card_insert_le (x t.succ) (Uset x k)
        omega

/-- A sequence takes at most one more value than it has distinct (unordered) steps. -/
lemma nv_le_steps (x : Fin (n + 1) → α) :
    nv x ≤ ((univ : Finset (Fin n)).image fun t => s(x t.castSucc, x t.succ)).card + 1 := by
  have h1 : nv x = (Uset x n).card := by
    unfold nv Uset
    congr 1
    rw [filter_true_of_mem fun t _ => Nat.lt_succ_iff.1 t.2]
  have h2 : Edset x n = (univ : Finset (Fin n)).image fun t => s(x t.castSucc, x t.succ) := by
    unfold Edset
    rw [filter_true_of_mem fun t _ => t.2]
  rw [h1, ← h2]
  exact U_Ed x n le_rfl

end Seq

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

lemma card_Ms_le (x : Fin (u.length + 1) → α) (j : Fin s) : (Ms u x j).card ≤ u.length :=
  le_trans (le_trans (single_le_sum (f := fun j => (Ms u x j).card) (fun _ _ => Nat.zero_le _)
    (mem_univ j)) (Nat.le_add_left _ _)) (sum_card_le u x)

/-- A path has at most one more vertex than edges. -/
lemma nv_le_sum_card (x : Fin (u.length + 1) → α) :
    nv x ≤ ∑ i, (Es u x i).card + ∑ j, (Ms u x j).card + 1 := by
  have hsub : ((univ : Finset (Fin u.length)).image fun t => s(x t.castSucc, x t.succ)) ⊆
      (univ.biUnion fun i => (Es u x i).image fun p : α × α => s(p.1, p.2)) ∪
        univ.biUnion (Ms u x) := by
    intro p hp
    obtain ⟨t, -, rfl⟩ := mem_image.1 hp
    rcases hl : u.get t with ⟨i, b⟩ | j
    · refine mem_union_left _ (mem_biUnion.2 ⟨i, mem_univ _, ?_⟩)
      cases b
      · exact mem_image.2 ⟨(x t.castSucc, x t.succ),
          mem_union_right _ (mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩), rfl⟩
      · exact mem_image.2 ⟨(x t.succ, x t.castSucc),
          mem_union_left _ (mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩), Sym2.eq_swap⟩
    · exact mem_union_right _ (mem_biUnion.2 ⟨j, mem_univ _,
        mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩⟩)
  have h1 := nv_le_steps x
  have h2 := card_le_card hsub
  have h3 := card_union_le (univ.biUnion fun i => (Es u x i).image fun p : α × α => s(p.1, p.2))
    (univ.biUnion (Ms u x))
  have h4 : (univ.biUnion fun i => (Es u x i).image fun p : α × α => s(p.1, p.2)).card ≤
      ∑ i, (Es u x i).card :=
    card_biUnion_le.trans (sum_le_sum fun i _ => card_image_le)
  have h5 : (univ.biUnion (Ms u x)).card ≤ ∑ j, (Ms u x j).card := card_biUnion_le
  omega

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

/-- Every colouring has at most one more vertex than edges. -/
lemma nv_le_Ecount_succ (u : List (Lt r s)) (c : Fin (u.length + 1) → Fin (u.length + 1)) :
    nv c ≤ Ecount u c + 1 :=
  nv_le_sum_card u c

/-! ## The polynomials -/

/-- `1 - a X`. -/
def lin (a : ℝ) : ℝ[X] := 1 - C a * X

lemma natDegree_lin (a : ℝ) : (lin a).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

lemma eval_lin (a x : ℝ) : (lin a).eval x = 1 - a * x := by simp [lin]

lemma natDegree_prod_lin (S : Finset ℕ) (a : ℕ → ℝ) :
    (∏ l ∈ S, lin (a l)).natDegree ≤ S.card :=
  (natDegree_prod_le _ _).trans ((sum_le_sum fun l _ => natDegree_lin _).trans (by simp))

/-- `∏_{l<k} (1 - l X)`. -/
def PA (k : ℕ) : ℝ[X] := ∏ l ∈ range k, lin (l : ℝ)

/-- `∏_{l<k} (1 - (2l+1) X)`. -/
def PB (k : ℕ) : ℝ[X] := ∏ l ∈ range k, lin (2 * (l : ℝ) + 1)

/-- `∏_{k≤l<q} (1 - l X)`. -/
def PA' (k q : ℕ) : ℝ[X] := ∏ l ∈ Ico k q, lin (l : ℝ)

/-- `∏_{k≤l<q} (1 - (2l+1) X)`. -/
def PB' (k q : ℕ) : ℝ[X] := ∏ l ∈ Ico k q, lin (2 * (l : ℝ) + 1)

lemma PA_mul (k q : ℕ) (h : k ≤ q) : PA k * PA' k q = PA q :=
  prod_range_mul_prod_Ico _ h

lemma PB_mul (k q : ℕ) (h : k ≤ q) : PB k * PB' k q = PB q :=
  prod_range_mul_prod_Ico _ h

lemma eval_PA (k : ℕ) (x : ℝ) : (PA k).eval x = ∏ l ∈ range k, (1 - (l : ℝ) * x) := by
  simp [PA, eval_prod, eval_lin]

lemma eval_PB (k : ℕ) (x : ℝ) :
    (PB k).eval x = ∏ l ∈ range k, (1 - (2 * (l : ℝ) + 1) * x) := by
  simp [PB, eval_prod, eval_lin]

lemma desc_eq (N k : ℕ) (hN : 1 ≤ N) :
    (N.descFactorial k : ℝ) = (N : ℝ) ^ k * (PA k).eval (1 / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [eval_PA]
  rcases Nat.lt_or_ge N k with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h, prod_eq_zero (mem_range.2 h), mul_zero]
    · simp
    · field_simp; simp
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
      show (N : ℝ) ^ k = ∏ _l ∈ range k, (N : ℝ) by simp, ← prod_mul_distrib]
    refine prod_congr rfl fun l hl => ?_
    have := mem_range.1 hl
    rw [Nat.cast_sub (by omega)]
    field_simp

lemma match_eq (N k : ℕ) (hN : 1 ≤ N) :
    ∏ l ∈ range k, ((N : ℝ) - 2 * l - 1) = (N : ℝ) ^ k * (PB k).eval (1 / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [eval_PB, show (N : ℝ) ^ k = ∏ _l ∈ range k, (N : ℝ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  field_simp
  ring

lemma PA_ne (N q : ℕ) (hN : 1 ≤ N) (hq : q ≤ N) : (PA q).eval (1 / (N : ℝ)) ≠ 0 := by
  intro h
  have := desc_eq N q hN
  rw [h, mul_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt] at this
  omega

lemma PB_ne (N q : ℕ) (hN : 1 ≤ N) (hE : Even N) : (PB q).eval (1 / (N : ℝ)) ≠ 0 := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [eval_PB, prod_ne_zero_iff]
  intro l _ h
  have h2 : (N : ℝ) = 2 * l + 1 := by
    field_simp at h
    linarith
  have h3 : N = 2 * l + 1 := by exact_mod_cast h2
  obtain ⟨m, hm⟩ := hE
  omega

lemma gq_bounds (r s q : ℕ) (hq : 1 ≤ q) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / (4 * ((r : ℝ) + s + 1) * (q : ℝ) ^ 2))) :
    1 / 2 ≤ ((PA q) ^ r * (PB q) ^ s).eval x ∧ ((PA q) ^ r * (PB q) ^ s).eval x ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hR : (0 : ℝ) < (r : ℝ) + s + 1 := by positivity
  set δ : ℝ := 1 / (2 * ((r : ℝ) + s + 1) * q) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have h2 : 2 * (q : ℝ) * x ≤ δ := by
    calc 2 * (q : ℝ) * x ≤ 2 * q * (1 / (4 * ((r : ℝ) + s + 1) * (q : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ = δ := by rw [hδ]; field_simp; ring
  have hnδ : ((q * (r + s) : ℕ) : ℝ) * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    nlinarith
  have hf : ∀ c : ℝ, 0 ≤ c → c ≤ 2 * q → 1 - δ ≤ 1 - c * x ∧ 1 - c * x ≤ 1 := by
    intro c hc0 hc
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hc hx0]
    · nlinarith [mul_nonneg hc0 hx0]
  have h1δ : 0 ≤ 1 - δ := by linarith
  have hA : (1 - δ) ^ q ≤ (PA q).eval x ∧ (PA q).eval x ≤ 1 := by
    rw [eval_PA]
    have hl : ∀ l ∈ range q, 1 - δ ≤ 1 - (l : ℝ) * x ∧ 1 - (l : ℝ) * x ≤ 1 := by
      intro l hl
      have : (l : ℝ) < q := by exact_mod_cast mem_range.1 hl
      exact hf l (by positivity) (by linarith)
    constructor
    · calc (1 - δ) ^ q = ∏ _l ∈ range q, (1 - δ) := by simp
        _ ≤ _ := prod_le_prod (fun _ _ => h1δ) (fun l hl' => (hl l hl').1)
    · exact prod_le_one (fun l hl' => h1δ.trans (hl l hl').1) (fun l hl' => (hl l hl').2)
  have hB : (1 - δ) ^ q ≤ (PB q).eval x ∧ (PB q).eval x ≤ 1 := by
    rw [eval_PB]
    have hl : ∀ l ∈ range q, 1 - δ ≤ 1 - (2 * (l : ℝ) + 1) * x ∧
        1 - (2 * (l : ℝ) + 1) * x ≤ 1 := by
      intro l hl
      have : (l : ℝ) + 1 ≤ q := by exact_mod_cast mem_range.1 hl
      exact hf _ (by positivity) (by linarith)
    constructor
    · calc (1 - δ) ^ q = ∏ _l ∈ range q, (1 - δ) := by simp
        _ ≤ _ := prod_le_prod (fun _ _ => h1δ) (fun l hl' => (hl l hl').1)
    · exact prod_le_one (fun l hl' => h1δ.trans (hl l hl').1) (fun l hl' => (hl l hl').2)
  have hp : 0 ≤ (1 - δ) ^ q := pow_nonneg h1δ _
  rw [eval_mul, eval_pow, eval_pow]
  constructor
  · have hb := one_add_mul_le_pow (a := -δ) (by linarith) (q * (r + s))
    calc (1 : ℝ) / 2 ≤ 1 + ((q * (r + s) : ℕ) : ℝ) * (-δ) := by linarith
      _ ≤ (1 + -δ) ^ (q * (r + s)) := hb
      _ = ((1 - δ) ^ q) ^ r * ((1 - δ) ^ q) ^ s := by
          rw [← sub_eq_add_neg, pow_mul, pow_add]
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hp hA.1 _) (pow_le_pow_left₀ hp hB.1 _)
          (pow_nonneg hp _) (pow_nonneg (hp.trans hA.1) _)
  · exact mul_le_one₀ (pow_le_one₀ (hp.trans hA.1) hA.2) (pow_nonneg (hp.trans hB.1) _)
      (pow_le_one₀ (hp.trans hB.1) hB.2)

/-! ## The polynomial of a colouring -/

/-- The numerator polynomial of a colouring (for the common denominator `PA q ^ r * PB q ^ s`). -/
def fpoly (u : List (Lt r s)) (q : ℕ) (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℝ[X] :=
  X ^ (Ecount u c + 1 - nv c) * PA (nv c) * (∏ i, PA' (Es u c i).card q) *
    ∏ j, PB' (Ms u c j).card q

lemma natDegree_fpoly (u : List (Lt r s)) (q : ℕ) (hq : 1 ≤ q) (hL : u.length ≤ q)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) :
    (fpoly u q c).natDegree ≤ (r + s + 2) * q := by
  have hv := nv_le_Ecount_succ u c
  have he : ∀ i, (Es u c i).card ≤ q := fun i => (card_Es_le u c i).trans hL
  have hm : ∀ j, (Ms u c j).card ≤ q := fun j => (card_Ms_le u c j).trans hL
  have h1 : (X ^ (Ecount u c + 1 - nv c) : ℝ[X]).natDegree ≤ Ecount u c + 1 - nv c :=
    natDegree_X_pow_le _
  have h2 : (PA (nv c)).natDegree ≤ nv c := by
    have := natDegree_prod_lin (range (nv c)) (fun l => (l : ℝ))
    rwa [card_range] at this
  have h3 : (∏ i, PA' (Es u c i).card q).natDegree ≤ ∑ i, (q - (Es u c i).card) := by
    refine (natDegree_prod_le _ _).trans (sum_le_sum fun i _ => ?_)
    have := natDegree_prod_lin (Ico (Es u c i).card q) (fun l => (l : ℝ))
    rwa [Nat.card_Ico] at this
  have h4 : (∏ j, PB' (Ms u c j).card q).natDegree ≤ ∑ j, (q - (Ms u c j).card) := by
    refine (natDegree_prod_le _ _).trans (sum_le_sum fun j _ => ?_)
    have := natDegree_prod_lin (Ico (Ms u c j).card q) (fun l => 2 * (l : ℝ) + 1)
    rwa [Nat.card_Ico] at this
  have h5 : ∑ i, (q - (Es u c i).card) + ∑ i, (Es u c i).card = r * q := by
    rw [← sum_add_distrib, sum_congr rfl fun i _ => Nat.sub_add_cancel (he i)]
    simp
  have h6 : ∑ j, (q - (Ms u c j).card) + ∑ j, (Ms u c j).card = s * q := by
    rw [← sum_add_distrib, sum_congr rfl fun j _ => Nat.sub_add_cancel (hm j)]
    simp
  have h7 : Ecount u c = ∑ i, (Es u c i).card + ∑ j, (Ms u c j).card := rfl
  have h8 : (fpoly u q c).natDegree ≤
      (Ecount u c + 1 - nv c) + nv c + ∑ i, (q - (Es u c i).card) +
        ∑ j, (q - (Ms u c j).card) := by
    unfold fpoly
    refine natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans (add_le_add
      (natDegree_mul_le.trans (add_le_add h1 h2)) h3)) h4)
  have h9 : (r + s + 2) * q = r * q + s * q + 2 * q := by ring
  omega

lemma wt_eq (u : List (Lt r s)) (q N : ℕ) (hL : u.length ≤ q) (hq : q ≤ N) (hN : 1 ≤ N)
    (hA : Adm s N) (c : Fin (u.length + 1) → Fin (u.length + 1)) :
    wt u N c = N * ((fpoly u q c).eval (1 / (N : ℝ)) /
      ((PA q) ^ r * (PB q) ^ s).eval (1 / (N : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hv := nv_le_Ecount_succ u c
  have he : ∀ i, (Es u c i).card ≤ q := fun i => (card_Es_le u c i).trans hL
  have hm : ∀ j, (Ms u c j).card ≤ q := fun j => (card_Ms_le u c j).trans hL
  have h7 : Ecount u c = ∑ i, (Es u c i).card + ∑ j, (Ms u c j).card := rfl
  set x : ℝ := 1 / (N : ℝ) with hx
  have e1 : ∏ i, (N.descFactorial (Es u c i).card : ℝ) =
      (N : ℝ) ^ (∑ i, (Es u c i).card) * ∏ i, (PA (Es u c i).card).eval x := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => desc_eq N _ hN
  have e2 : ∏ j, ∏ l ∈ range (Ms u c j).card, ((N : ℝ) - 2 * l - 1) =
      (N : ℝ) ^ (∑ j, (Ms u c j).card) * ∏ j, (PB (Ms u c j).card).eval x := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => match_eq N _ hN
  have eg : ((PA q) ^ r * (PB q) ^ s).eval x =
      ((∏ i, (PA (Es u c i).card).eval x) * ∏ i, (PA' (Es u c i).card q).eval x) *
        ((∏ j, (PB (Ms u c j).card).eval x) * ∏ j, (PB' (Ms u c j).card q).eval x) := by
    rw [eval_mul, eval_pow, eval_pow, ← prod_mul_distrib, ← prod_mul_distrib,
      show (PA q).eval x ^ r = ∏ _i : Fin r, (PA q).eval x by simp,
      show (PB q).eval x ^ s = ∏ _j : Fin s, (PB q).eval x by simp]
    congr 1
    · exact prod_congr rfl fun i _ => by rw [← eval_mul, PA_mul _ _ (he i)]
    · exact prod_congr rfl fun j _ => by rw [← eval_mul, PB_mul _ _ (hm j)]
  have ef : (fpoly u q c).eval x =
      x ^ (Ecount u c + 1 - nv c) * (PA (nv c)).eval x *
        (∏ i, (PA' (Es u c i).card q).eval x) * ∏ j, (PB' (Ms u c j).card q).eval x := by
    simp [fpoly, eval_mul, eval_pow, eval_prod]
  have hA' : (∏ i, (PA' (Es u c i).card q).eval x) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro i _
    have := PA_ne N q hN hq
    rw [← PA_mul _ _ (he i), eval_mul] at this
    exact right_ne_zero_of_mul this
  have hB' : (∏ j, (PB' (Ms u c j).card q).eval x) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro j _
    have hE : Even N := by
      rcases hA with h0 | hE
      · subst h0; exact j.elim0
      · exact hE
    have := PB_ne N q hN hE
    rw [← PB_mul _ _ (hm j), eval_mul] at this
    exact right_ne_zero_of_mul this
  unfold wt
  rw [e1, e2, eg, ef, desc_eq N (nv c) hN]
  set Se := ∑ i, (Es u c i).card
  set Sm := ∑ j, (Ms u c j).card
  set k := Ecount u c + 1 - nv c with hk
  set a := (PA (nv c)).eval x
  set QA := ∏ i, (PA (Es u c i).card).eval x
  set QA' := ∏ i, (PA' (Es u c i).card q).eval x
  set QB := ∏ j, (PB (Ms u c j).card).eval x
  set QB' := ∏ j, (PB' (Ms u c j).card q).eval x
  have hkv : Se + Sm + 1 = nv c + k := by omega
  have hNx : (N : ℝ) * x = 1 := by rw [hx]; field_simp
  have hK : (N : ℝ) ^ Se * (N : ℝ) ^ Sm * ((N : ℝ) * x ^ k) = (N : ℝ) ^ nv c := by
    calc (N : ℝ) ^ Se * (N : ℝ) ^ Sm * ((N : ℝ) * x ^ k)
        = (N : ℝ) ^ (Se + Sm + 1) * x ^ k := by ring
      _ = (N : ℝ) ^ nv c * ((N : ℝ) * x) ^ k := by rw [hkv, pow_add, mul_pow]; ring
      _ = (N : ℝ) ^ nv c := by rw [hNx, one_pow, mul_one]
  have hNE : (N : ℝ) ^ Se * (N : ℝ) ^ Sm ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hN0) (pow_ne_zero _ hN0)
  calc (N : ℝ) ^ nv c * a / ((N : ℝ) ^ Se * QA * ((N : ℝ) ^ Sm * QB))
      = ((N : ℝ) ^ Se * (N : ℝ) ^ Sm) * (((N : ℝ) * x ^ k) * a) /
          (((N : ℝ) ^ Se * (N : ℝ) ^ Sm) * (QA * QB)) := by rw [← hK]; ring
    _ = ((N : ℝ) * x ^ k) * a / (QA * QB) := mul_div_mul_left _ _ hNE
    _ = (((N : ℝ) * x ^ k) * a * (QA' * QB')) / ((QA * QB) * (QA' * QB')) :=
        (mul_div_mul_right _ _ (mul_ne_zero hA' hB')).symm
    _ = (N : ℝ) * (x ^ k * a * QA' * QB' / (QA * QA' * (QB * QB'))) := by ring

/-! ## Rationality -/

theorem rational (r s q : ℕ) (hq : 1 ≤ q) :
    ∃ gq : ℝ[X], gq.natDegree ≤ (r + s) * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / (4 * ((r : ℝ) + s + 1) * (q : ℝ) ^ 2)),
        1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ g : G r s, len g ≤ q → ∃ f : ℝ[X], f.natDegree ≤ (r + s + 2) * q ∧
        ∀ N : ℕ, Adm s N → q ≤ N →
          expFix r s N g = N * (f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ))) := by
  refine ⟨(PA q) ^ r * (PB q) ^ s, ?_, fun x hx => gq_bounds r s q hq x hx, ?_⟩
  · have hPA : (PA q).natDegree ≤ q := by
      have := natDegree_prod_lin (range q) (fun l => (l : ℝ))
      rwa [card_range] at this
    have hPB : (PB q).natDegree ≤ q := by
      have := natDegree_prod_lin (range q) (fun l => 2 * (l : ℝ) + 1)
      rwa [card_range] at this
    calc ((PA q) ^ r * (PB q) ^ s).natDegree
        ≤ ((PA q) ^ r).natDegree + ((PB q) ^ s).natDegree := natDegree_mul_le
      _ ≤ r * q + s * q := add_le_add (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hPA))
          (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hPB))
      _ = (r + s) * q := by ring
  · obtain ⟨nf, -, hnf, -, hlen⟩ := nf_exists r s
    intro g hg
    have hL : (nf g).length ≤ q := by rw [← hlen]; exact hg
    refine ⟨∑ c ∈ CG (nf g), fpoly (nf g) q c, ?_, ?_⟩
    · exact natDegree_sum_le_of_forall_le _ _ fun c _ => natDegree_fpoly (nf g) q hq hL c
    · intro N hA hqN
      have hN : 1 ≤ N := hq.trans hqN
      have h : ∀ ω : Om r s N, act ω g = wordPerm ω (nf g) := fun ω => by
        rw [← act_wprod, hnf]
      have h' : expFix r s N g = expFixW r s N (nf g) := by
        unfold expFix expFixW
        simp only [h]
      rw [h', expect_formula (nf g) N hN hA (hL.trans hqN), eval_finsetSum, sum_div, mul_sum]
      exact sum_congr rfl fun c _ => wt_eq (nf g) q N hL hqN hN hA c

end BordenaveCollins.PartC
end
end

section
open Polynomial
open BordenaveCollins

theorem solution (r s q : ℕ) (hq : 1 ≤ q) :
    ∃ gq : ℝ[X], gq.natDegree ≤ (r + s) * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / (4 * ((r : ℝ) + s + 1) * (q : ℝ) ^ 2)),
        1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ g : G r s, len g ≤ q → ∃ f : ℝ[X], f.natDegree ≤ (r + s + 2) * q ∧
        ∀ N : ℕ, Adm s N → q ≤ N →
          expFix r s N g = N * (f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ))) :=
  BordenaveCollins.PartC.rational r s q hq

end
