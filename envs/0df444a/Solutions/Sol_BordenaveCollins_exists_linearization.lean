-- Prove2me | solution 1 for BordenaveCollins.exists_linearization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:20:41.500218+00:00
-- url     : https://prove2.me/submissions/560668de-db11-4543-9957-ff93a381d634

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_DerandSq_permOp
import Definitions.Def_BordenaveCollinsFactorization
import Theorems.Thm_BordenaveCollins_Pisier_exists_factorization_of_norm_evalP_lt

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

/-! ## Colourings of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPerm ω (u.drop t) y`). -/

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

end BordenaveCollins

end
end

section
/-!
# Part O1, general lemmas: `AccessibleMaps.tensorOp`, `DerandSq.permOp`, `DerandSq.leftReg`,
the projection `Q`, and `opOf` as an additive map.
-/

open Finset
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartO1

open AccessibleMaps

/-! ## `tensorOp` -/

section Tensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tensorOp_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin n) :
    (tensorOp A T x) a = ∑ b, A a b • T (x b) := by
  simp [tensorOp, inject, Pi.single_apply]

theorem op_ext {n : ℕ} (X Y : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (h : ∀ x a, X x a = Y x a) : X = Y :=
  ContinuousLinearMap.ext fun x => PiLp.ext fun a => h x a

theorem tensorOp_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (S T : H →L[ℂ] H) :
    tensorOp A S * tensorOp B T = tensorOp (A * B) (S * T) := by
  refine op_ext _ _ fun x a => ?_
  simp only [mul_apply_eq_comp, tensorOp_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem tensorOp_add_left {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  refine op_ext _ _ fun x a => ?_
  simp [tensorOp_apply, add_smul, Finset.sum_add_distrib]

theorem tensorOp_zero_left {n : ℕ} (T : H →L[ℂ] H) :
    tensorOp (0 : Matrix (Fin n) (Fin n) ℂ) T = 0 := by
  refine op_ext _ _ fun x a => ?_
  simp [tensorOp_apply]

variable [CompleteSpace H]

end Tensor

/-! ## Trace of a tensor operator -/

/-! ## Permutation operators -/

/-! ## The left regular representation -/

end BordenaveCollins.PartO1

end
end

section
/-!
# Part O1: the projection `Q` onto `1^⊥` and `opOf` as an additive map.
-/

open Finset
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartO1

open AccessibleMaps DerandSq

/-! ## The projection -/

/-! ## `opOf` -/

section OpOf
variable {r s D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem opOf_eq_sum (π : G r s → H →L[ℂ] H) (x : MG D r s) :
    opOf π x = x.coeff.sum fun g A => tensorOp A (π g) := rfl

theorem opOf_zero (π : G r s → H →L[ℂ] H) : opOf π (0 : MG D r s) = 0 := by
  simp [opOf]

theorem opOf_add' (π : G r s → H →L[ℂ] H) (x y : MG D r s) :
    opOf π (x + y) = opOf π x + opOf π y := by
  rw [opOf_eq_sum, opOf_eq_sum, opOf_eq_sum, MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun g => tensorOp_zero_left (π g))
    (fun g A B => tensorOp_add_left A B (π g))

theorem opOf_single (π : G r s → H →L[ℂ] H) (g : G r s) (A : Matrix (Fin D) (Fin D) ℂ) :
    opOf π (MonoidAlgebra.single g A) = tensorOp A (π g) := by
  rw [opOf_eq_sum, MonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (tensorOp_zero_left (π g))

theorem opOf_mul' (π : G r s →* (H →L[ℂ] H)) (x y : MG D r s) :
    opOf (fun g => π g) (x * y) = opOf (fun g => π g) x * opOf (fun g => π g) y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, opOf_zero, zero_mul]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, opOf_add', opOf_add', h₁, h₂, add_mul]
  | single g A =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, opOf_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, opOf_add', opOf_add', h₁, h₂, mul_add]
    | single h B =>
      rw [MonoidAlgebra.single_mul_single, opOf_single, opOf_single, opOf_single, tensorOp_mul,
        map_mul]

end OpOf

end BordenaveCollins.PartO1

end
end

section
/-!
# Part O1: operators (the Blueprint stubs)
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartO1

open AccessibleMaps DerandSq

variable {r s : ℕ}

/-! ## The four `opOf` stubs -/

section Ops

variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem opOf_mul (π : G r s →* (H →L[ℂ] H)) (x y : MG D r s) :
    opOf (fun g => π g) (x * y) = opOf (fun g => π g) x * opOf (fun g => π g) y :=
  opOf_mul' π x y

end Ops

/-! ## The model operators -/

/-! ## The trace `τ` -/

/-! ## Word length of the support of a polynomial -/

end BordenaveCollins.PartO1

end
end

section
/-!
# The statements proved in Part O1, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

section Ops

variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem opOf_mul (π : G r s →* (H →L[ℂ] H)) (x y : MG D r s) :
    opOf (fun g => π g) (x * y) = opOf (fun g => π g) x * opOf (fun g => π g) y :=
  PartO1.opOf_mul π x y

end Ops

end BordenaveCollins

end
end

section
/-!
# PartF helpers: algebra and norms of `tOp` and `amp`
-/

noncomputable section

open scoped InnerProductSpace
open Matrix

namespace BordenaveCollins.Pisier.PartF

section Ops

variable {H₁ H₂ H₃ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃]

lemma tOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂)
    (x : PiLp 2 (fun _ : Fin n => H₁)) (a : Fin m) :
    tOp A T x a = ∑ b, A a b • T (x b) := by
  simp only [tOp]
  simp [Pi.single_apply, Finset.sum_ite_eq']

lemma tOp_smul {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂) :
    tOp (c • A) T = c • tOp A T := by
  ext x a
  simp [tOp_apply, Finset.smul_sum, smul_smul]

@[simp] lemma tOp_zero {m n : ℕ} (T : H₁ →L[ℂ] H₂) :
    tOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  ext x a
  simp [tOp_apply]

@[simp] lemma tOp_zero_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    tOp A (0 : H₁ →L[ℂ] H₂) = 0 := by
  ext x a
  simp [tOp_apply]

lemma tOp_comp {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (S : H₂ →L[ℂ] H₃) (T : H₁ →L[ℂ] H₂) :
    (tOp A S).comp (tOp B T) = tOp (A * B) (S.comp T) := by
  ext x a
  simp only [ContinuousLinearMap.comp_apply, tOp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

lemma tOp_one_one {n : ℕ} :
    tOp (1 : Matrix (Fin n) (Fin n) ℂ) (ContinuousLinearMap.id ℂ H₁) =
      ContinuousLinearMap.id ℂ _ := by
  ext x a
  simp only [tOp_apply, ContinuousLinearMap.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

end Ops

end BordenaveCollins.Pisier.PartF
end
end

section
/-!
# PartF: the factorization theorem (MATH.md Lemma 1 + the Hahn–Banach half of Lemma 11)

The set of framed contractive chains is absolutely convex (`isChain_absConvex`); on its span
its gauge is a seminorm. Hahn–Banach gives a functional `f` with `|f| ≤ gauge` and
`f(evalP e y) = gauge(evalP e y)`. Its coefficients `F w i j = f(Eᵢⱼ ⊗ e(w))` satisfy
`ChainBound` and `FRel`, so `core_bound` bounds the gauge by the operator norm.
-/

noncomputable section

open scoped InnerProductSpace Pointwise
open Matrix

namespace BordenaveCollins.Pisier.PartF

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem factorization (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {D : ℕ}
    (y : List ι →₀ Matrix (Fin D) (Fin D) ℂ) (c : ℝ) (hc : ‖evalP e y‖ < c) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D),
      1 ≤ q ∧ evalP e y = c • gChainOn e Dim A q h₁ hq ∧
        ∀ j ∈ Finset.Icc 1 q, ‖amp e (A j)‖ ≤ 1 := by
  classical
  exact BordenaveCollins.Pisier.exists_factorization_of_norm_evalP_lt e hU y c hc

end BordenaveCollins.Pisier.PartF
end
end

section
/-!
# Part P1 helpers: the left-regular letters, chains of linear factors, zero-padding

* The letters `Option (Lt r s)` act on `ℓ²(G r s)` by `leftReg (genO l)`; they are unitary and
  closed under inverse (`eL_unitary`), and `regOp x` is a formal polynomial in them
  (`regOp_eq_evalP`).
* `Xprod L m = X_1 ⋯ X_m = ∑_i Bprod L m i ⊗ λ(iprod i)` (`Xprod_expand`).
* Zero-padding of rectangular blocks to a common size (`mkLin`), periodic extension.
-/

open Finset
open scoped Classical InnerProductSpace

noncomputable section

namespace BordenaveCollins.PartP1

open Pisier Pisier.PartF

variable {r s : ℕ}

/-! ## The left-regular representation -/

section Reg
variable {Γ : Type*} [Group Γ]

lemma leftReg_apply (g : Γ) (f : DerandSq.L2 Γ) (h : Γ) :
    (DerandSq.leftReg g f) h = f (g⁻¹ * h) := rfl

lemma leftReg_mul (g g' : Γ) :
    DerandSq.leftReg g * DerandSq.leftReg g' = DerandSq.leftReg (g * g') := by
  ext f h
  simp only [ContinuousLinearMap.mul_apply, leftReg_apply, mul_inv_rev, mul_assoc]

lemma leftReg_one : DerandSq.leftReg (1 : Γ) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma leftReg_norm (g : Γ) (f : DerandSq.L2 Γ) : ‖DerandSq.leftReg g f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (Equiv.mulLeft g⁻¹).tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal)

lemma leftReg_mem_unitary (g : Γ) :
    DerandSq.leftReg g ∈ unitary (DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) := by
  let u : (DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ)ˣ :=
    { val := DerandSq.leftReg g
      inv := DerandSq.leftReg g⁻¹
      val_inv := by rw [leftReg_mul, mul_inv_cancel, leftReg_one]
      inv_val := by rw [leftReg_mul, inv_mul_cancel, leftReg_one] }
  refine IsUnit.mem_unitary_of_star_mul_self ⟨u, rfl⟩ ?_
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (leftReg_norm g)

lemma star_leftReg (g : Γ) : star (DerandSq.leftReg g) = DerandSq.leftReg g⁻¹ := by
  have h1 := Unitary.star_mul_self_of_mem (leftReg_mem_unitary g)
  have h2 : DerandSq.leftReg g * DerandSq.leftReg g⁻¹ = 1 := by
    rw [leftReg_mul, mul_inv_cancel, leftReg_one]
  calc star (DerandSq.leftReg g)
      = star (DerandSq.leftReg g) * (DerandSq.leftReg g * DerandSq.leftReg g⁻¹) := by
        rw [h2, mul_one]
    _ = DerandSq.leftReg g⁻¹ := by rw [← mul_assoc, h1, one_mul]

/-- The basis vector `δ_g`. -/
def dlt (g : Γ) : DerandSq.L2 Γ := lp.single 2 g (1 : ℂ)

lemma leftReg_dlt_one_apply (h g : Γ) :
    (DerandSq.leftReg h (dlt (1 : Γ))) g = if g = h then 1 else 0 := by
  rw [leftReg_apply, dlt]
  by_cases hg : g = h
  · subst hg
    rw [if_pos rfl, inv_mul_cancel, lp.single_apply_self]
  · rw [if_neg hg, lp.single_apply_ne]
    intro h'
    exact hg (by rw [← mul_one h, ← h', mul_inv_cancel_left])

end Reg

/-! ## `tensorOp` is `tOp` -/

section Tensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma tensorOp_eq_tOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    AccessibleMaps.tensorOp A T = tOp A T := by
  ext x a
  rw [tOp_apply]
  simp [AccessibleMaps.tensorOp, AccessibleMaps.inject, Pi.single_apply, Finset.sum_apply]

lemma tOp_one_one' {n : ℕ} : tOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 :=
  tOp_one_one

lemma tOp_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (S T : H →L[ℂ] H) :
    tOp A S * tOp B T = tOp (A * B) (S * T) :=
  tOp_comp A B S T

end Tensor

/-! ## The letters -/

/-- `ℓ²(G)`. -/
abbrev HG (r s : ℕ) := DerandSq.L2 (G r s)

/-- The letters `1, u_i, u_i⁻¹, m_j` in the left-regular representation. -/
def eL (r s : ℕ) : Option (Lt r s) → HG r s →L[ℂ] HG r s :=
  fun l => DerandSq.leftReg (genO l)

def eL_unitary (r s : ℕ) : UnitaryLetters (eL r s) where
  o := none
  e_o := leftReg_one
  inv := Option.map bar
  e_inv := by
    intro l
    cases l with
    | none =>
      show DerandSq.leftReg (1 : G r s) = star (DerandSq.leftReg (1 : G r s))
      rw [leftReg_one, star_one]
    | some a =>
      show DerandSq.leftReg (genL (bar a)) = star (DerandSq.leftReg (genL a))
      rw [genL_bar, star_leftReg]
  unitary := fun l => leftReg_mem_unitary _

lemma evalW_eL (w : List (Option (Lt r s))) :
    evalW (eL r s) w = DerandSq.leftReg ((w.map genO).prod) := by
  induction w with
  | nil => simp [evalW, leftReg_one]
  | cons a w ih =>
    simp only [evalW, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, ← leftReg_mul]
    rfl

/-- `regOp x` is a formal polynomial in the letters. -/
lemma regOp_eq_evalP {D : ℕ} (x : MG D r s) :
    ∃ y : List (Option (Lt r s)) →₀ Matrix (Fin D) (Fin D) ℂ, evalP (eL r s) y = regOp x := by
  obtain ⟨nf, -, hnf, -, -⟩ := nf_exists r s
  let f : G r s → List (Option (Lt r s)) := fun g => (nf g).map some
  have hfg : ∀ g, ((f g).map genO).prod = g := by
    intro g
    have : (f g).map genO = (nf g).map genL := by
      simp only [f, List.map_map]
      rfl
    rw [this]
    exact hnf g
  have hf : Function.Injective f := fun g g' h => by rw [← hfg g, ← hfg g', h]
  refine ⟨x.coeff.mapDomain f, ?_⟩
  unfold evalP regOp opOf
  rw [Finsupp.mapDomain_support_of_injective hf, Finset.sum_image (fun a _ b _ h => hf h)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finsupp.mapDomain_apply hf, evalW_eL, hfg, tensorOp_eq_tOp]

/-! ## Chains of the linear factors -/

lemma Xop_eq (L : Lin r s) (j : ℕ) : Xop L j = amp (eL r s) (L.B j) := by
  simp only [Xop, tensorOp_eq_tOp, amp, eL]

/-- `X_1 X_2 ⋯ X_m`. -/
def Xprod (L : Lin r s) (m : ℕ) :
    PiLp 2 (fun _ : Fin L.Dm => HG r s) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => HG r s) :=
  ((List.range m).map fun j => Xop L (j + 1)).prod

lemma Xprod_succ (L : Lin r s) (m : ℕ) : Xprod L (m + 1) = Xprod L m * Xop L (m + 1) := by
  simp [Xprod, List.range_succ]

lemma Bprod_snoc (L : Lin r s) (m : ℕ) (i : Fin m → Option (Lt r s)) (a : Option (Lt r s)) :
    Bprod L (m + 1) (Fin.snoc i a) = Bprod L m i * L.B (m + 1) a := by
  unfold Bprod
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

lemma iprod_snoc (m : ℕ) (i : Fin m → Option (Lt r s)) (a : Option (Lt r s)) :
    iprod (Fin.snoc i a : Fin (m + 1) → Option (Lt r s)) = iprod i * genO a := by
  unfold iprod
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

def snocEquiv (m : ℕ) :
    (Fin m → Option (Lt r s)) × Option (Lt r s) ≃ (Fin (m + 1) → Option (Lt r s)) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last m))
  left_inv p := by simp
  right_inv f := by simp

theorem Xprod_expand (L : Lin r s) (m : ℕ) :
    Xprod L m = ∑ i : Fin m → Option (Lt r s),
      tOp (Bprod L m i) (DerandSq.leftReg (iprod i)) := by
  induction m with
  | zero =>
    rw [Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)]
    simp [Xprod, Bprod, iprod, leftReg_one, tOp_one_one']
  | succ m ih =>
    rw [Xprod_succ, ih, Xop_eq, amp, Finset.sum_mul]
    rw [← Fintype.sum_equiv (snocEquiv m) (fun p => tOp (Bprod L (m + 1) (snocEquiv m p))
        (DerandSq.leftReg (iprod (snocEquiv m p)))) _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [snocEquiv, Equiv.coe_fn_mk, Bprod_snoc, iprod_snoc, ← leftReg_mul]
    exact tOp_mul _ _ _ _

lemma Xop_add_q (L : Lin r s) (j : ℕ) : Xop L (j + L.q) = Xop L j := by
  simp [Xop, L.periodic]

lemma Xop_add_mul (L : Lin r s) (j k : ℕ) : Xop L (j + k * L.q) = Xop L j := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul, ← add_assoc, Xop_add_q, ih]

lemma Xprod_add (L : Lin r s) (a b : ℕ) :
    Xprod L (a + b) = Xprod L a * ((List.range b).map fun j => Xop L (a + j + 1)).prod := by
  simp only [Xprod, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 3

theorem Xprod_mul_q (L : Lin r s) (p : ℕ) : Xprod L (p * L.q) = Xprod L L.q ^ p := by
  induction p with
  | zero => simp [Xprod]
  | succ p ih =>
    rw [Nat.succ_mul, Xprod_add, ih, pow_succ]
    congr 1
    simp only [Xprod]
    congr 1
    apply List.map_congr_left
    intro j _
    have := Xop_add_mul L (j + 1) p
    rw [← this]
    congr 1
    ring

/-! ## Padding by zeros -/

/-- The zero-padding (or truncation) matrix. -/
def Emat (n m : ℕ) : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun x y => if (x : ℕ) = y then 1 else 0

theorem Emat_mul {a b c : ℕ} (h : a ≤ b) : Emat b c * Emat a b = Emat a c := by
  ext x y
  simp only [Matrix.mul_apply, Emat, Matrix.of_apply]
  rw [Finset.sum_eq_single (⟨y, lt_of_lt_of_le y.2 h⟩ : Fin b)]
  · simp
  · intro z _ hz
    have : (z : ℕ) ≠ y := fun h' => hz (Fin.ext h')
    simp [this]
  · simp

theorem Emat_self (n : ℕ) : Emat n n = 1 := by
  ext x y
  simp [Emat, Matrix.one_apply, Fin.ext_iff]

section Pad
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Embedding of `n` copies into `m` copies by padding with zeros (or truncation). -/
def padOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (n m : ℕ) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H) :=
  tOp (Emat n m) (1 : H →L[ℂ] H)

theorem padOp_apply (n m : ℕ) (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    padOp H n m x a = if h : (a : ℕ) < n then x ⟨a, h⟩ else 0 := by
  rw [padOp, tOp_apply]
  by_cases h : (a : ℕ) < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨a, h⟩ : Fin n)]
    · simp [Emat]
    · intro b _ hb
      have : (a : ℕ) ≠ b := fun h' => hb (Fin.ext h'.symm)
      simp [Emat, this]
    · simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : (a : ℕ) ≠ b := fun h' => h (h' ▸ b.2)
    simp [Emat, this]

theorem padOp_norm_le (n m : ℕ) (x : PiLp 2 (fun _ : Fin n => H)) : ‖padOp H n m x‖ ≤ ‖x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  set g : ℕ → ℝ := fun k => if h : k < n then ‖x ⟨k, h⟩‖ ^ 2 else 0 with hg
  have h1 : ∑ a : Fin m, ‖padOp H n m x a‖ ^ 2 = ∑ k ∈ Finset.range m, g k := by
    rw [← Fin.sum_univ_eq_sum_range g m]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [padOp_apply]
    by_cases h : (a : ℕ) < n <;> simp [hg, h]
  have h2 : ∑ b : Fin n, ‖x b‖ ^ 2 = ∑ k ∈ Finset.range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hg]
  rw [h1, h2]
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    by_cases h : k < n <;> simp [hg, h]
  calc ∑ k ∈ Finset.range m, g k = ∑ k ∈ Finset.range m ∩ Finset.range n, g k := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun k hk hk' => ?_
        have : ¬ k < n := fun h => hk' (Finset.mem_inter.mpr ⟨hk, Finset.mem_range.mpr h⟩)
        simp [hg, this]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun k _ _ => hg0 k)

theorem padOp_opNorm_le (n m : ℕ) : ‖padOp H n m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using padOp_norm_le n m x

theorem padOp_comp (n m : ℕ) (h : n ≤ m) :
    (padOp H m n).comp (padOp H n m) = ContinuousLinearMap.id ℂ _ := by
  unfold padOp
  rw [tOp_comp, Emat_mul h, Emat_self]
  exact tOp_one_one

end Pad

end BordenaveCollins.PartP1

end
end

section
/-!
# Part P1 helpers: the padded linearization and the transfer to the group algebra

* `mkLin`: rectangular blocks `A_j` padded by zeros to a common size and extended periodically.
* `transfer_trace`: if `regOp x` is the corner of `X_1 ⋯ X_q`, then
  `tr (x^p)_g = ∑_{i : iprod i = g} tr (Bprod L (p q) i)`.
-/

open Finset
open scoped Classical InnerProductSpace

noncomputable section

namespace BordenaveCollins.PartP1

open Pisier Pisier.PartF

variable {r s : ℕ}

/-! ## Amplifications -/

lemma tOp_conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {a b c e' : ℕ}
    (E1 : Matrix (Fin c) (Fin a) ℂ) (E2 : Matrix (Fin b) (Fin e') ℂ)
    (C : Matrix (Fin a) (Fin b) ℂ) (W : H →L[ℂ] H) :
    (tOp E1 (1 : H →L[ℂ] H)).comp ((tOp C W).comp (tOp E2 (1 : H →L[ℂ] H))) =
      tOp (E1 * C * E2) W := by
  rw [tOp_comp, tOp_comp, Matrix.mul_assoc]
  rfl

lemma amp_conj {a b c e' : ℕ} (E1 : Matrix (Fin c) (Fin a) ℂ) (E2 : Matrix (Fin b) (Fin e') ℂ)
    (A : Option (Lt r s) → Matrix (Fin a) (Fin b) ℂ) :
    amp (eL r s) (fun l => E1 * A l * E2) =
      (tOp E1 (1 : HG r s →L[ℂ] HG r s)).comp
        ((amp (eL r s) A).comp (tOp E2 (1 : HG r s →L[ℂ] HG r s))) := by
  ext x : 1
  simp only [amp, ← tOp_conj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    map_sum]

lemma amp_smul (c : ℂ) {m n : ℕ} (X : Option (Lt r s) → Matrix (Fin m) (Fin n) ℂ) :
    amp (eL r s) (fun l => c • X l) = c • amp (eL r s) X := by
  simp only [amp, tOp_smul, Finset.smul_sum]

lemma gChain_smul (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Option (Lt r s) → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (c : ℂ) (t : ℕ) :
    ∀ k : ℕ, gChain (eL r s) Dim (fun j l => c • A j l) t k = c ^ k • gChain (eL r s) Dim A t k
  | 0 => by simp [gChain]
  | k + 1 => by
    rw [gChain, gChain, gChain_smul Dim A c t k, amp_smul,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, pow_succ]

/-! ## The padded linearization -/

def jj (q j : ℕ) : ℕ := (j + q - 1) % q + 1

theorem jj_add (q : ℕ) (hq : 1 ≤ q) (j : ℕ) : jj q (j + q) = jj q j := by
  unfold jj
  have : j + q + q - 1 = (j + q - 1) + q := by omega
  rw [this, Nat.add_mod_right]

theorem jj_mem (q : ℕ) (hq : 1 ≤ q) (j : ℕ) : 1 ≤ jj q j ∧ jj q j ≤ q := by
  unfold jj
  have := Nat.mod_lt (j + q - 1) hq
  omega

theorem jj_self (q : ℕ) (hq : 1 ≤ q) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ q) : jj q j = j := by
  unfold jj
  have : j + q - 1 = (j - 1) + q := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

def DmOf (q : ℕ) (Dim : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range (q + 2), Dim j

theorem Dim_le_DmOf (q : ℕ) (Dim : ℕ → ℕ) (a : ℕ) (h : a ≤ q + 1) : Dim a ≤ DmOf q Dim :=
  Finset.single_le_sum (f := Dim) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

/-- The padded block `E A_k E'`. -/
def Bf (q : ℕ) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Option (Lt r s) → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (k : ℕ)
    (l : Option (Lt r s)) : Matrix (Fin (DmOf q Dim)) (Fin (DmOf q Dim)) ℂ :=
  Emat (Dim k) (DmOf q Dim) * A k l * Emat (DmOf q Dim) (Dim (k + 1))

lemma Bf_row_zero (q : ℕ) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Option (Lt r s) → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (k : ℕ)
    (l : Option (Lt r s)) (a b : Fin (DmOf q Dim)) (ha : Dim k ≤ (a : ℕ)) :
    Bf q Dim A k l a b = 0 := by
  have h : ∀ z : Fin (Dim k), ¬ ((a : ℕ) = z) := fun z hz => by have := z.2; omega
  simp [Bf, Matrix.mul_apply, Emat, h]

def mkLin (q : ℕ) (hq : 1 ≤ q) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Option (Lt r s) → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) : Lin r s where
  q := q
  hq := hq
  Dm := DmOf q Dim
  B := fun j l => Bf q Dim A (jj q j) l
  periodic := by
    intro j l
    show Bf q Dim A (jj q (j + q)) l = Bf q Dim A (jj q j) l
    rw [jj_add q hq]

section MkLin
variable (q : ℕ) (hq : 1 ≤ q) (Dim : ℕ → ℕ)
  (A : ∀ j : ℕ, Option (Lt r s) → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)

theorem Xop_pad_of (j k : ℕ) (hjk : jj q j = k) :
    Xop (mkLin q hq Dim A) j =
      (padOp (HG r s) (Dim k) (DmOf q Dim)).comp
        ((amp (eL r s) (A k)).comp (padOp (HG r s) (DmOf q Dim) (Dim (k + 1)))) := by
  subst hjk
  rw [Xop_eq]
  exact amp_conj (Emat (Dim (jj q j)) (DmOf q Dim)) (Emat (DmOf q Dim) (Dim (jj q j + 1)))
    (A (jj q j))

theorem Xop_norm_le (R : ℝ)
    (hA : ∀ j ∈ Finset.Icc 1 q, ‖amp (eL r s) (A j)‖ ≤ R) (j : ℕ) :
    ‖Xop (mkLin q hq Dim A) j‖ ≤ R := by
  have hj := jj_mem q hq j
  rw [Xop_pad_of q hq Dim A j (jj q j) rfl]
  calc _ ≤ ‖padOp (HG r s) (Dim (jj q j)) (DmOf q Dim)‖ *
        (‖amp (eL r s) (A (jj q j))‖ * ‖padOp (HG r s) (DmOf q Dim) (Dim (jj q j + 1))‖) := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (R * 1) := by
        have h1 := padOp_opNorm_le (H := HG r s) (Dim (jj q j)) (DmOf q Dim)
        have h2 := padOp_opNorm_le (H := HG r s) (DmOf q Dim) (Dim (jj q j + 1))
        have h3 := hA (jj q j) (Finset.mem_Icc.mpr hj)
        have hR : 0 ≤ R := (norm_nonneg _).trans h3
        gcongr
    _ = R := by ring

theorem Xprod_pad : ∀ m : ℕ, 1 ≤ m → m ≤ q →
    Xprod (mkLin q hq Dim A) m =
      (padOp (HG r s) (Dim 1) (DmOf q Dim)).comp
        ((gChain (eL r s) Dim A 1 m).comp (padOp (HG r s) (DmOf q Dim) (Dim (1 + m)))) := by
  intro m hm1
  induction m, hm1 using Nat.le_induction with
  | base =>
    intro hmq
    have : Xprod (mkLin q hq Dim A) 1 = Xop (mkLin q hq Dim A) 1 := by simp [Xprod]
    rw [this, Xop_pad_of q hq Dim A 1 1 (jj_self q hq 1 le_rfl hmq)]
    rfl
  | succ m hm ih =>
    intro hmq
    have hj : jj q (m + 1) = 1 + m := by
      rw [jj_self q hq (m + 1) (by omega) hmq]; omega
    rw [Xprod_succ, Xop_pad_of q hq Dim A (m + 1) (1 + m) hj, ih (by omega)]
    have hc := padOp_comp (H := HG r s) (Dim (1 + m)) (DmOf q Dim)
      (Dim_le_DmOf q Dim (1 + m) (by omega))
    have key : ((padOp (HG r s) (Dim 1) (DmOf q Dim)).comp
        ((gChain (eL r s) Dim A 1 m).comp (padOp (HG r s) (DmOf q Dim) (Dim (1 + m))))).comp
        ((padOp (HG r s) (Dim (1 + m)) (DmOf q Dim)).comp
          ((amp (eL r s) (A (1 + m))).comp (padOp (HG r s) (DmOf q Dim) (Dim (1 + m + 1))))) =
        (padOp (HG r s) (Dim 1) (DmOf q Dim)).comp
        ((gChain (eL r s) Dim A 1 (m + 1)).comp
          (padOp (HG r s) (DmOf q Dim) (Dim (1 + (m + 1))))) := by
      ext x : 1
      simp only [ContinuousLinearMap.comp_apply]
      have := congrArg (fun f => f (amp (eL r s) (A (1 + m)) (padOp (HG r s) (DmOf q Dim)
        (Dim (1 + m + 1)) x))) hc
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
      rw [this]
      rfl
    exact key

end MkLin

/-! ## Compression to the top-left block -/

section Compress
variable (L : Lin r s) (D : ℕ) (hDm : D ≤ L.Dm)
  (hS1 : ∀ l (a b : Fin L.Dm), D ≤ (a : ℕ) → L.B 1 l a b = 0)

include hS1 in
theorem Xop_one_zero (x : PiLp 2 (fun _ : Fin L.Dm => HG r s)) (a : Fin L.Dm)
    (ha : D ≤ (a : ℕ)) : Xop L 1 x a = 0 := by
  rw [Xop_eq]
  simp [amp, tOp_apply, hS1 _ a _ ha]

include hS1 in
theorem Xprod_zero : ∀ m : ℕ, 1 ≤ m → ∀ (x : PiLp 2 (fun _ : Fin L.Dm => HG r s))
    (a : Fin L.Dm), D ≤ (a : ℕ) → Xprod L m x a = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro x a ha
    have : Xprod L 1 = Xop L 1 := by simp [Xprod]
    rw [this]
    exact Xop_one_zero L D hS1 x a ha
  | succ m hm ih =>
    intro x a ha
    rw [Xprod_succ]
    exact ih _ a ha

include hDm in
theorem pad_absorb (z : PiLp 2 (fun _ : Fin L.Dm => HG r s))
    (hz : ∀ a : Fin L.Dm, D ≤ (a : ℕ) → z a = 0) :
    padOp (HG r s) D L.Dm (padOp (HG r s) L.Dm D z) = z := by
  refine PiLp.ext fun a => ?_
  rw [padOp_apply]
  by_cases h : (a : ℕ) < D
  · rw [dif_pos h, padOp_apply, dif_pos (lt_of_lt_of_le h hDm)]
  · rw [dif_neg h, hz a (not_lt.mp h)]

include hS1 hDm in
theorem compress_absorb (m : ℕ) (hm : 1 ≤ m) (x : PiLp 2 (fun _ : Fin L.Dm => HG r s)) :
    padOp (HG r s) D L.Dm (padOp (HG r s) L.Dm D (Xprod L m x)) = Xprod L m x :=
  pad_absorb L D hDm _ (Xprod_zero L D hS1 m hm x)

/-- The compression of `X_1 ⋯ X_q` to the top-left `D × D` block. -/
def Tcomp : PiLp 2 (fun _ : Fin D => HG r s) →L[ℂ] PiLp 2 (fun _ : Fin D => HG r s) :=
  (padOp (HG r s) L.Dm D).comp ((Xprod L L.q).comp (padOp (HG r s) D L.Dm))

include hS1 hDm in
theorem Tcomp_pow : ∀ p : ℕ, 1 ≤ p →
    Tcomp L D ^ p =
      (padOp (HG r s) L.Dm D).comp ((Xprod L L.q ^ p).comp (padOp (HG r s) D L.Dm)) := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base => simp [Tcomp]
  | succ p hp ih =>
    rw [pow_succ, ih]
    ext x : 1
    simp only [Tcomp, ContinuousLinearMap.comp_apply, mul_apply_eq_comp, Function.comp_apply,
      pow_succ]
    rw [compress_absorb L D hDm hS1 L.q L.hq]

/-- The compression of a matrix to the top-left `D × D` block. -/
def blk (Dm D : ℕ) (C : Matrix (Fin Dm) (Fin Dm) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Emat Dm D * C * Emat D Dm

theorem pad_Xprod_pad (m : ℕ) :
    (padOp (HG r s) L.Dm D).comp ((Xprod L m).comp (padOp (HG r s) D L.Dm)) =
      ∑ i : Fin m → Option (Lt r s),
        tOp (blk L.Dm D (Bprod L m i)) (DerandSq.leftReg (iprod i)) := by
  rw [Xprod_expand]
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := tOp_conj (Emat L.Dm D) (Emat D L.Dm) (Bprod L m i) (DerandSq.leftReg (iprod i))
  rw [blk, ← this]
  rfl

include hS1 hDm in
theorem Tcomp_pow_expand (p : ℕ) (hp : 1 ≤ p) :
    Tcomp L D ^ p = ∑ i : Fin (p * L.q) → Option (Lt r s),
        tOp (blk L.Dm D (Bprod L (p * L.q) i)) (DerandSq.leftReg (iprod i)) := by
  rw [Tcomp_pow L D hDm hS1 p hp, ← Xprod_mul_q, pad_Xprod_pad]

include hS1 in
theorem Bprod_row_zero (m : ℕ) (hm : 1 ≤ m) (i : Fin m → Option (Lt r s)) (a b : Fin L.Dm)
    (ha : D ≤ (a : ℕ)) : Bprod L m i a b = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold Bprod
  rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  have := hS1 (i 0) a y ha
  simp only [Fin.val_zero, zero_add]
  rw [this, zero_mul]

end Compress

theorem blk_apply {Dm D : ℕ} (hD : D ≤ Dm) (C : Matrix (Fin Dm) (Fin Dm) ℂ) (a b : Fin D) :
    blk Dm D C a b = C (Fin.castLE hD a) (Fin.castLE hD b) := by
  simp only [blk, Matrix.mul_apply, Emat, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.castLE hD b)]
  · rw [Finset.sum_eq_single (Fin.castLE hD a)]
    · simp
    · intro z _ hz
      have : ¬ ((a : ℕ) = z) := fun h' => hz (Fin.ext h'.symm)
      simp [this]
    · simp
  · intro z _ hz
    have : ¬ ((z : ℕ) = b) := fun h' => hz (Fin.ext h')
    simp [this]
  · simp

theorem trace_blk {Dm D : ℕ} (hD : D ≤ Dm) (C : Matrix (Fin Dm) (Fin Dm) ℂ)
    (hrow : ∀ a b : Fin Dm, D ≤ (a : ℕ) → C a b = 0) : (blk Dm D C).trace = C.trace := by
  set g : ℕ → ℂ := fun k => if h : k < Dm then C ⟨k, h⟩ ⟨k, h⟩ else 0 with hg
  have h1 : (blk Dm D C).trace = ∑ k ∈ Finset.range D, g k := by
    rw [← Fin.sum_univ_eq_sum_range g D]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.diag_apply, blk_apply hD]
    have : (a : ℕ) < Dm := lt_of_lt_of_le a.2 hD
    simp [hg, this, Fin.castLE]
  have h2 : C.trace = ∑ k ∈ Finset.range Dm, g k := by
    rw [← Fin.sum_univ_eq_sum_range g Dm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hg, Matrix.diag_apply]
  rw [h1, h2]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hD) fun k hk hk' => ?_
  have hk1 : k < Dm := Finset.mem_range.mp hk
  have hk2 : D ≤ k := not_lt.mp fun h => hk' (Finset.mem_range.mpr h)
  simp only [hg, dif_pos hk1]
  exact hrow _ _ hk2

/-! ## Reading off coefficients: the left-regular representation is faithful -/

section Coeff
variable {D : ℕ}

/-- The vector `e_b ⊗ δ_1`. -/
def vec (r s D : ℕ) (b : Fin D) : PiLp 2 (fun _ : Fin D => HG r s) :=
  WithLp.toLp 2 (Pi.single b (dlt (1 : G r s)))

/-- The matrix coefficient `⟨e_a ⊗ δ_g, T (e_b ⊗ δ_1)⟩`. -/
def ev (a b : Fin D) (g : G r s)
    (T : PiLp 2 (fun _ : Fin D => HG r s) →L[ℂ] PiLp 2 (fun _ : Fin D => HG r s)) : ℂ :=
  (T (vec r s D b) a) g

lemma ev_add (a b : Fin D) (g : G r s)
    (T S : PiLp 2 (fun _ : Fin D => HG r s) →L[ℂ] PiLp 2 (fun _ : Fin D => HG r s)) :
    ev a b g (T + S) = ev a b g T + ev a b g S := rfl

lemma ev_zero (a b : Fin D) (g : G r s) :
    ev a b g (0 : PiLp 2 (fun _ : Fin D => HG r s) →L[ℂ] PiLp 2 (fun _ : Fin D => HG r s)) = 0 :=
  rfl

lemma ev_sum {ι : Type*} (a b : Fin D) (g : G r s) (S : Finset ι)
    (T : ι → PiLp 2 (fun _ : Fin D => HG r s) →L[ℂ] PiLp 2 (fun _ : Fin D => HG r s)) :
    ev a b g (∑ i ∈ S, T i) = ∑ i ∈ S, ev a b g (T i) := by
  induction S using Finset.induction_on with
  | empty => simp [ev_zero]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ev_add, ih]

lemma ev_tOp (a b : Fin D) (g h : G r s) (A : Matrix (Fin D) (Fin D) ℂ) :
    ev a b g (tOp A (DerandSq.leftReg h)) = if g = h then A a b else 0 := by
  unfold ev
  rw [tOp_apply, Finset.sum_eq_single b]
  · have : (vec r s D b) b = dlt (1 : G r s) := by simp [vec]
    rw [this, lp.coeFn_smul, Pi.smul_apply, leftReg_dlt_one_apply]
    simp
  · intro b' _ hb'
    have : (vec r s D b) b' = 0 := by simp [vec, hb']
    rw [this, map_zero, smul_zero]
  · simp

theorem coeff_of_regOp_eq {m : ℕ} (z : MG D r s)
    (C : (Fin m → Option (Lt r s)) → Matrix (Fin D) (Fin D) ℂ)
    (h : regOp z = ∑ i, tOp (C i) (DerandSq.leftReg (iprod i))) (g : G r s) (a b : Fin D) :
    z.coeff g a b = ∑ i, if iprod i = g then C i a b else 0 := by
  have h' := congrArg (ev a b g) h
  have hz : regOp z = ∑ h ∈ z.coeff.support, tOp (z.coeff h) (DerandSq.leftReg h) := by
    unfold regOp opOf
    simp only [tensorOp_eq_tOp]
  rw [hz, ev_sum, ev_sum] at h'
  simp only [ev_tOp] at h'
  rw [Finset.sum_ite_eq] at h'
  have hg : (if g ∈ z.coeff.support then z.coeff g a b else 0) = z.coeff g a b := by
    split_ifs with hmem
    · rfl
    · rw [Finsupp.notMem_support_iff.mp hmem]; rfl
  rw [hg] at h'
  rw [h']
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : iprod i = g
  · rw [if_pos hi, if_pos hi.symm]
  · rw [if_neg hi, if_neg (Ne.symm hi)]

/-- The left-regular representation as a monoid homomorphism. -/
def lamHom (r s : ℕ) : G r s →* (HG r s →L[ℂ] HG r s) where
  toFun g := DerandSq.leftReg g
  map_one' := leftReg_one
  map_mul' g h := (leftReg_mul g h).symm

theorem regOp_mul (x y : MG D r s) : regOp (x * y) = regOp x * regOp y :=
  opOf_mul (lamHom r s) x y

theorem regOp_pow (x : MG D r s) : ∀ p : ℕ, 1 ≤ p → regOp (x ^ p) = regOp x ^ p := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base => simp
  | succ p hp ih => rw [pow_succ, regOp_mul, ih, pow_succ]

/-- The transfer: if `regOp x` is the corner of `X_1 ⋯ X_q`, the traces of the coefficients of
`x^p` are sums of traces of products of the blocks. -/
theorem transfer_trace (L : Lin r s) (hDm : D ≤ L.Dm)
    (hS1 : ∀ l (a b : Fin L.Dm), D ≤ (a : ℕ) → L.B 1 l a b = 0) (x : MG D r s)
    (hx : regOp x = Tcomp L D) (p : ℕ) (hp : 1 ≤ p) (g : G r s) :
    Matrix.trace ((x ^ p).coeff g) =
      ∑ i : Fin (p * L.q) → Option (Lt r s),
        if iprod i = g then (Bprod L (p * L.q) i).trace else 0 := by
  have h1 : regOp (x ^ p) = ∑ i : Fin (p * L.q) → Option (Lt r s),
      tOp (blk L.Dm D (Bprod L (p * L.q) i)) (DerandSq.leftReg (iprod i)) := by
    rw [regOp_pow x p hp, hx, Tcomp_pow_expand L D hDm hS1 p hp]
  have h2 := coeff_of_regOp_eq (x ^ p) _ h1 g
  have hm : 1 ≤ p * L.q := Nat.mul_pos hp L.hq
  simp only [Matrix.trace, Matrix.diag_apply]
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : iprod i = g
  · simp only [if_pos hi]
    have := trace_blk hDm (Bprod L (p * L.q) i)
      (fun a b ha => Bprod_row_zero L D hS1 (p * L.q) hm i a b ha)
    simpa only [Matrix.trace, Matrix.diag_apply] using this
  · simp only [if_neg hi, Finset.sum_const_zero]

end Coeff

/-! ## The corner of the padded chain -/

section Corner
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma pad_pad_rc {a b m : ℕ} (h : a = b) (ham : a ≤ m) :
    (padOp H m b).comp (padOp H a m) = reindexCopies (finCongr h) := by
  subst h
  rw [padOp_comp a m ham]
  ext x i
  simp [reindexCopies]

lemma pad_pad_rc' {a b m : ℕ} (h : a = b) (hbm : b ≤ m) :
    (padOp H m a).comp (padOp H b m) = reindexCopies (finCongr h).symm := by
  subst h
  rw [padOp_comp a m hbm]
  ext x i
  simp [reindexCopies]

end Corner

lemma comp_aux {E₁ E₂ E₃ E₄ E₅ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂]
    [NormedAddCommGroup E₃] [InnerProductSpace ℂ E₃] [NormedAddCommGroup E₄] [InnerProductSpace ℂ E₄]
    [NormedAddCommGroup E₅] [InnerProductSpace ℂ E₅] (c : ℝ)
    (P2 : E₂ →L[ℂ] E₁) (P1 : E₃ →L[ℂ] E₂) (Gc : E₄ →L[ℂ] E₃) (P3 : E₂ →L[ℂ] E₄)
    (P4 : E₅ →L[ℂ] E₂) :
    c • ((P2.comp P1).comp (Gc.comp (P3.comp P4))) =
      P2.comp (((c : ℂ) • (P1.comp (Gc.comp P3))).comp P4) := by
  ext x
  simp [Complex.coe_smul]

theorem corner_eq {D : ℕ}
    (T : PiLp 2 (fun _ : Fin D => HG r s) →L[ℂ] PiLp 2 (fun _ : Fin D => HG r s))
    (c : ℝ) (hc : 0 < c) (q : ℕ) (hq1 : 1 ≤ q) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Option (Lt r s) → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
    (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D)
    (hT : T = c • gChainOn (eL r s) Dim A q h₁ hq) :
    T = Tcomp (mkLin q hq1 Dim (fun j l => ((c ^ (1 / (q : ℝ)) : ℝ) : ℂ) • A j l)) D := by
  set σ : ℝ := c ^ (1 / (q : ℝ)) with hσ
  have hsq : (σ : ℂ) ^ q = (c : ℂ) := by
    rw [← Complex.ofReal_pow, hσ, one_div, Real.rpow_inv_natCast_pow hc.le (by omega)]
  have hD1 : D ≤ DmOf q Dim := h₁ ▸ Dim_le_DmOf q Dim 1 (by omega)
  have hD2 : Dim (1 + q) ≤ DmOf q Dim := Dim_le_DmOf q Dim (1 + q) (by omega)
  have e1 := pad_pad_rc (H := HG r s) h₁ (h₁ ▸ hD1 : Dim 1 ≤ DmOf q Dim)
  have e2 := pad_pad_rc' (H := HG r s) hq hD1
  have hX : Xprod (mkLin q hq1 Dim (fun j l => (σ : ℂ) • A j l)) q =
      (c : ℂ) • ((padOp (HG r s) (Dim 1) (DmOf q Dim)).comp
        ((gChain (eL r s) Dim A 1 q).comp (padOp (HG r s) (DmOf q Dim) (Dim (1 + q))))) := by
    rw [Xprod_pad q hq1 Dim _ q hq1 le_rfl, gChain_smul, hsq, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]
  have hTc : Tcomp (mkLin q hq1 Dim (fun j l => (σ : ℂ) • A j l)) D =
      (padOp (HG r s) (DmOf q Dim) D).comp
        (((c : ℂ) • ((padOp (HG r s) (Dim 1) (DmOf q Dim)).comp
          ((gChain (eL r s) Dim A 1 q).comp (padOp (HG r s) (DmOf q Dim) (Dim (1 + q)))))).comp
          (padOp (HG r s) D (DmOf q Dim))) := by
    show (padOp (HG r s) (DmOf q Dim) D).comp
      ((Xprod (mkLin q hq1 Dim (fun j l => (σ : ℂ) • A j l)) q).comp
        (padOp (HG r s) D (DmOf q Dim))) = _
    rw [hX]
    rfl
  rw [hTc, hT, gChainOn, ← e1, ← e2]
  exact comp_aux c _ _ _ _ _

end BordenaveCollins.PartP1

end
end

section
/-!
# Part P1: Pisier's linearization for `F_r * Γ_s` and the first-order bound

* `linearization_alg`: Pisier's factorization (general unitary letters, `Pisier.PartF.factorization`)
  applied to the left-regular letters, padded to a common block size, and transferred to the
  group algebra through the faithfulness of the left-regular representation.
* `nu_one_bound`: from `linearization_alg` and the stub `BordenaveCollins.core_bound`.
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartP1

variable {r s : ℕ}

theorem linearization_alg {D : ℕ} (x : MG D r s) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : Lin r s, (∀ j, ‖Xop L j‖ ≤ (‖regOp x‖ + δ) ^ (1 / (L.q : ℝ))) ∧
      ∀ p : ℕ, 1 ≤ p → ∀ g : G r s,
        Matrix.trace ((x ^ p).coeff g) =
          ∑ i : Fin (p * L.q) → Option (Lt r s),
            if iprod i = g then (Bprod L (p * L.q) i).trace else 0 := by
  obtain ⟨y, hy⟩ := regOp_eq_evalP x
  set c : ℝ := ‖regOp x‖ + δ with hc
  have hc0 : 0 < c := by positivity
  have hlt : ‖Pisier.evalP (eL r s) y‖ < c := by rw [hy]; linarith
  obtain ⟨q, Dim, A, h₁, hq, hq1, heq, hA⟩ :=
    Pisier.PartF.factorization (eL r s) (eL_unitary r s) y c hlt
  set σ : ℝ := c ^ (1 / (q : ℝ)) with hσ
  have hσ0 : 0 ≤ σ := Real.rpow_nonneg hc0.le _
  refine ⟨mkLin q hq1 Dim (fun j l => (σ : ℂ) • A j l), ?_, ?_⟩
  · intro j
    refine Xop_norm_le q hq1 Dim _ σ ?_ j
    intro k hk
    rw [amp_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hσ0]
    calc σ * ‖Pisier.amp (eL r s) (A k)‖ ≤ σ * 1 := mul_le_mul_of_nonneg_left (hA k hk) hσ0
      _ = σ := mul_one σ
  · have hx : regOp x = Tcomp (mkLin q hq1 Dim (fun j l => (σ : ℂ) • A j l)) D :=
      corner_eq (regOp x) c hc0 q hq1 Dim A h₁ hq (hy.symm.trans heq)
    have hDm : D ≤ DmOf q Dim := h₁.ge.trans (Dim_le_DmOf q Dim 1 (by omega))
    have hS1 : ∀ l (a b : Fin (DmOf q Dim)), D ≤ (a : ℕ) →
        Bf q Dim (fun j l => (σ : ℂ) • A j l) (jj q 1) l a b = 0 := by
      intro l a b ha
      rw [jj_self q hq1 1 le_rfl hq1]
      exact Bf_row_zero q Dim _ 1 l a b (h₁.le.trans ha)
    intro p hp g
    exact transfer_trace (mkLin q hq1 Dim (fun j l => (σ : ℂ) • A j l)) hDm hS1 x hx p hp g

end BordenaveCollins.PartP1

end
end

section
open scoped Classical
open BordenaveCollins

theorem solution {r s : ℕ} {D : ℕ} (x : MG D r s) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : Lin r s, (∀ j, ‖Xop L j‖ ≤ (‖regOp x‖ + δ) ^ (1 / (L.q : ℝ))) ∧
      ∀ p : ℕ, 1 ≤ p → ∀ g : G r s,
        Matrix.trace ((x ^ p).coeff g) =
          ∑ i : Fin (p * L.q) → Option (Lt r s),
            if iprod i = g then (Bprod L (p * L.q) i).trace else 0 :=
  BordenaveCollins.PartP1.linearization_alg x δ hδ

end
