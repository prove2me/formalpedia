-- Prove2me | solution 1 for BordenaveCollins.tendsto_re_trTau_pow_rpow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:20:40.973431+00:00
-- url     : https://prove2.me/submissions/36eb6152-5565-4303-b7ad-ae9de2f4d2c7

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_DerandSq_permOp

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

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

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

end BordenaveCollins.PartF1
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

theorem tensorOp_one_one {n : ℕ} :
    tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  refine op_ext _ _ fun x a => ?_
  simp [tensorOp_apply, Matrix.one_apply]

variable [CompleteSpace H]

theorem star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp A.conjTranspose (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [tensorOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp [Matrix.conjTranspose_apply]

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

/-- `opOf π` as an additive map. -/
def opHom (D : ℕ) (π : G r s → H →L[ℂ] H) : MG D r s →+
    (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) where
  toFun := opOf π
  map_zero' := opOf_zero π
  map_add' := opOf_add' π

theorem opHom_apply (π : G r s → H →L[ℂ] H) (x : MG D r s) : opHom D π x = opOf π x := rfl

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

theorem opOf_one' (π : G r s →* (H →L[ℂ] H)) :
    opOf (fun g => π g) (1 : MG D r s) = 1 := by
  rw [MonoidAlgebra.one_def, opOf_single, map_one]
  exact tensorOp_one_one

theorem opOf_adj' [CompleteSpace H] (π : G r s → H →L[ℂ] H) (hπ : ∀ g, star (π g) = π g⁻¹)
    (x : MG D r s) : star (opOf π x) = opOf π (adj x) := by
  have h1 : opOf π (adj x) = x.coeff.sum fun g A => opOf π (MonoidAlgebra.single g⁻¹ A.conjTranspose) := by
    rw [← opHom_apply, adj]
    exact map_finsuppSum (opHom D π) _ _
  have hsum := fun (S : Finset (G r s))
      (f : G r s → (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H))) =>
    star_sum S f
  rw [h1, opOf_eq_sum, Finsupp.sum, Finsupp.sum, hsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [opOf_single, star_tensorOp, hπ]

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

theorem opOf_one (π : G r s →* (H →L[ℂ] H)) :
    opOf (fun g => π g) (1 : MG D r s) = 1 :=
  opOf_one' π

theorem opOf_adj (π : G r s → H →L[ℂ] H) (hπ : ∀ g, star (π g) = π g⁻¹) (x : MG D r s) :
    star (opOf π x) = opOf π (adj x) :=
  opOf_adj' π hπ x

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

theorem opOf_one (π : G r s →* (H →L[ℂ] H)) :
    opOf (fun g => π g) (1 : MG D r s) = 1 :=
  PartO1.opOf_one π

theorem opOf_adj (π : G r s → H →L[ℂ] H) (hπ : ∀ g, star (π g) = π g⁻¹) (x : MG D r s) :
    star (opOf π x) = opOf π (adj x) :=
  PartO1.opOf_adj π hπ x

end Ops

end BordenaveCollins

end
end

section
/-!
# Part L, first half: faithfulness of the trace (`faithful`)

`trTau y` is the vector state `D⁻¹ ∑_a ⟪e_a ⊗ δ_1, regOp y (e_a ⊗ δ_1)⟫`; it is faithful on
operators commuting with the right translations `1 ⊗ R_g`.
-/

open scoped InnerProductSpace
open Matrix Filter Topology
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartL

variable {r s : ℕ}

/-! ### Left and right translations on `ℓ²(Γ)` -/

section Gen

variable {Γ : Type*} [Group Γ]

lemma leftReg_apply (g : Γ) (f : DerandSq.L2 Γ) (h : Γ) :
    DerandSq.leftReg g f h = f (g⁻¹ * h) := rfl

lemma star_leftReg_gen (g : Γ) :
    star (DerandSq.leftReg g : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = DerandSq.leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma leftReg_one_gen : (DerandSq.leftReg (1 : Γ) : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma leftReg_mul_gen (a b : Γ) :
    (DerandSq.leftReg (a * b) : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) =
      DerandSq.leftReg a * DerandSq.leftReg b := by
  ext f h
  simp [leftReg_apply, mul_assoc]

/-- The right translation `(R_g f)(h) = f(h g)`. -/
def rightReg (g : Γ) : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun h => f (h * g), by
        have hf := (lp.memℓp f)
        rw [memℓp_gen_iff (by norm_num)] at hf
        show Memℓp (fun h : Γ => f (h * g)) 2
        rw [memℓp_gen_iff (by norm_num)]
        exact (Equiv.mulRight g).summable_iff.mpr hf⟩
      map_add' := fun f f' => by ext h; rfl
      map_smul' := fun c f => by ext h; rfl }
    1
    (by
      intro f
      rw [one_mul]
      apply le_of_eq
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      congr 1
      exact (Equiv.mulRight g).tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal))

lemma rightReg_apply (g : Γ) (f : DerandSq.L2 Γ) (h : Γ) :
    rightReg g f h = f (h * g) := rfl

lemma leftReg_rightReg_gen (a g : Γ) (f : DerandSq.L2 Γ) :
    DerandSq.leftReg a (rightReg g f) = rightReg g (DerandSq.leftReg a f) := by
  ext h
  simp only [leftReg_apply, rightReg_apply, mul_assoc]

/-- `δ_g`. -/
def delta (g : Γ) : DerandSq.L2 Γ := lp.single 2 g (1 : ℂ)

lemma rightReg_delta_one_gen (g : Γ) : rightReg g⁻¹ (delta 1) = delta g := by
  ext h
  simp only [rightReg_apply, delta, lp.single_apply, Pi.single_apply]
  by_cases hh : h = g
  · subst hh; simp
  · rw [if_neg (by intro h'; apply hh; simpa [mul_inv_eq_one] using h'), if_neg hh]

lemma leftReg_delta_one_gen (g : Γ) : DerandSq.leftReg g (delta 1) = delta g := by
  ext h
  simp only [leftReg_apply, delta, lp.single_apply, Pi.single_apply]
  by_cases hh : h = g
  · subst hh; simp
  · rw [if_neg (by intro h'; apply hh; exact (inv_mul_eq_one.mp h').symm), if_neg hh]

lemma inner_delta_gen (g : Γ) : ⟪delta (1 : Γ), delta g⟫_ℂ = if g = 1 then 1 else 0 := by
  unfold delta
  rw [lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply, eq_comm]

lemma hasSum_delta_gen (f : DerandSq.L2 Γ) : HasSum (fun g : Γ => (f g) • delta g) f := by
  have hs := lp.hasSum_single (E := fun _ : Γ => ℂ) (p := 2) (by norm_num) f
  have : ∀ g, lp.single 2 g (f g) = (f g) • delta g := by
    intro g
    rw [delta, ← lp.single_smul]; simp
  simpa only [this] using hs

end Gen

abbrev L2G (r s : ℕ) := DerandSq.L2 (G r s)

lemma star_leftReg (g : G r s) :
    star (DerandSq.leftReg g : L2G r s →L[ℂ] L2G r s) = DerandSq.leftReg g⁻¹ :=
  star_leftReg_gen g

/-- The left-regular representation as a monoid homomorphism. -/
def lregHom (r s : ℕ) : G r s →* (L2G r s →L[ℂ] L2G r s) where
  toFun g := DerandSq.leftReg g
  map_one' := leftReg_one_gen
  map_mul' a b := leftReg_mul_gen a b

lemma rightReg_delta_one (g : G r s) : rightReg g⁻¹ (delta 1) = delta g :=
  rightReg_delta_one_gen g

lemma leftReg_delta_one (g : G r s) : DerandSq.leftReg g (delta 1) = delta g :=
  leftReg_delta_one_gen g

lemma inner_delta (g : G r s) : ⟪delta (1 : G r s), delta g⟫_ℂ = if g = 1 then 1 else 0 :=
  inner_delta_gen g

/-! ### `D` copies -/

variable {D : ℕ}

abbrev EE (D r s : ℕ) := PiLp 2 (fun _ : Fin D => L2G r s)

lemma tensorOp_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Matrix (Fin D) (Fin D) ℂ) (T : H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin D => H)) (a : Fin D) :
    AccessibleMaps.tensorOp A T y a = ∑ b, A a b • T (y b) := by
  simp [AccessibleMaps.tensorOp, AccessibleMaps.inject, Finset.sum_apply]
  simp [Pi.single_apply]

/-- `1 ⊗ R_g`. -/
def U (D : ℕ) (g : G r s) : (EE D r s) →L[ℂ] (EE D r s) :=
  AccessibleMaps.tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) (rightReg g)

lemma U_apply (g : G r s) (y : EE D r s) (a : Fin D) : U D g y a = rightReg g (y a) := by
  rw [U, tensorOp_apply]
  simp [Matrix.one_apply]

lemma U_single (g : G r s) (a : Fin D) (x : L2G r s) :
    U D g (PiLp.single 2 a x) = PiLp.single 2 a (rightReg g x) := by
  classical
  ext b : 1
  rw [U_apply]
  by_cases h : b = a
  · subst h; simp
  · simp [PiLp.single_apply, h]

lemma commute_regOp_U (y : MG D r s) (g : G r s) : Commute (regOp y) (U D g) := by
  unfold regOp opOf
  apply Commute.sum_left
  intro w _
  ext v a : 2
  simp only [ContinuousLinearMap.mul_apply, tensorOp_apply, U_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [leftReg_rightReg_gen]

/-- A bounded operator vanishing on every `e_a ⊗ δ_g` is zero. -/
lemma eq_zero_of_single_delta (X : (EE D r s) →L[ℂ] (EE D r s))
    (hX : ∀ a g, X (PiLp.single 2 a (delta g)) = 0) : X = 0 := by
  classical
  have h1 : ∀ a (f : L2G r s), X (PiLp.single 2 a f) = 0 := by
    intro a f
    let L : L2G r s →L[ℂ] EE D r s := X.comp
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => L2G r s)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin D => L2G r s) a))
    have hL : ∀ x, L x = X (PiLp.single 2 a x) := fun x => rfl
    have hm := (hasSum_delta_gen f).mapL L
    have hz : ∀ g, L ((f g) • delta g) = 0 := by
      intro g
      rw [map_smul, hL, hX, smul_zero]
    simp only [hz] at hm
    rw [← hL]
    exact (hm.unique hasSum_zero)
  ext y : 1
  have : y = ∑ a, PiLp.single 2 a (y a) := by
    ext b; simp [PiLp.single_apply]
  rw [this, map_sum]
  simp [h1]

/-! ### The vector state -/

/-- `e_a ⊗ δ_e`. -/
abbrev vv (D r s : ℕ) (a : Fin D) : EE D r s := PiLp.single 2 a (delta 1)

lemma norm_vv (a : Fin D) : ‖(vv D r s a : EE D r s)‖ = 1 := by
  rw [vv, PiLp.norm_single, delta, lp.norm_single (by norm_num)]
  simp

/-- The vector state `D⁻¹ ∑_a ⟪e_a ⊗ δ_1, Y (e_a ⊗ δ_1)⟫`. -/
def tauOp (Y : (EE D r s) →L[ℂ] (EE D r s)) : ℂ :=
  (D : ℂ)⁻¹ * ∑ a : Fin D, ⟪vv D r s a, Y (vv D r s a)⟫_ℂ

lemma inner_vv_tensorOp (A : Matrix (Fin D) (Fin D) ℂ) (g : G r s) (a : Fin D) :
    ⟪vv D r s a, AccessibleMaps.tensorOp A (DerandSq.leftReg g) (vv D r s a)⟫_ℂ =
      if g = 1 then A a a else 0 := by
  classical
  rw [PiLp.inner_apply, Finset.sum_eq_single a]
  · rw [tensorOp_apply, Finset.sum_eq_single a]
    · simp only [PiLp.single_apply, if_true, inner_smul_right, leftReg_delta_one, inner_delta]
      split_ifs <;> simp
    · intro b _ hb
      simp [PiLp.single_apply, hb]
    · simp
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · simp

lemma trTau_eq_tauOp (y : MG D r s) : trTau y = tauOp (regOp y) := by
  classical
  unfold trTau tauOp regOp opOf
  congr 1
  simp only [ContinuousLinearMap.sum_apply, inner_sum, inner_vv_tensorOp]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero]
  by_cases h1 : (1 : G r s) ∈ y.coeff.support
  · simp [h1, Matrix.trace]
  · have : y.coeff 1 = 0 := Finsupp.notMem_support_iff.mp h1
    simp [h1, this]

lemma tauOp_re (Y : (EE D r s) →L[ℂ] (EE D r s)) :
    (tauOp Y).re = (D : ℝ)⁻¹ * ∑ a : Fin D, (⟪vv D r s a, Y (vv D r s a)⟫_ℂ).re := by
  unfold tauOp
  have h1 : ((D : ℂ)⁻¹) = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [h1, Complex.re_ofReal_mul, Complex.re_sum]

lemma re_tauOp_le_norm (Y : (EE D r s) →L[ℂ] (EE D r s)) : (tauOp Y).re ≤ ‖Y‖ := by
  rw [tauOp_re]
  have hb : ∀ a : Fin D, (⟪vv D r s a, Y (vv D r s a)⟫_ℂ).re ≤ ‖Y‖ := by
    intro a
    calc (⟪vv D r s a, Y (vv D r s a)⟫_ℂ).re ≤ ‖⟪vv D r s a, Y (vv D r s a)⟫_ℂ‖ :=
          Complex.re_le_norm _
      _ ≤ ‖vv D r s a‖ * ‖Y (vv D r s a)‖ := norm_inner_le_norm _ _
      _ ≤ ‖vv D r s a‖ * (‖Y‖ * ‖vv D r s a‖) := by
          gcongr; exact Y.le_opNorm _
      _ = ‖Y‖ := by rw [norm_vv]; ring
  calc (D : ℝ)⁻¹ * ∑ a : Fin D, (⟪vv D r s a, Y (vv D r s a)⟫_ℂ).re
      ≤ (D : ℝ)⁻¹ * ∑ _a : Fin D, ‖Y‖ := by gcongr with a; exact hb a
    _ = ((D : ℝ)⁻¹ * D) * ‖Y‖ := by simp; ring
    _ ≤ ‖Y‖ := by
        rcases Nat.eq_zero_or_pos D with h | h
        · simp [h]
        · rw [inv_mul_cancel₀ (by positivity), one_mul]

lemma re_tauOp_nonneg (X : (EE D r s) →L[ℂ] (EE D r s)) (hX : 0 ≤ X) : 0 ≤ (tauOp X).re := by
  have hpos : X.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive X).mp hX
  rw [tauOp_re]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hpos.re_inner_nonneg_right _)

lemma tauOp_sub (Y Z : (EE D r s) →L[ℂ] (EE D r s)) : tauOp (Z - Y) = tauOp Z - tauOp Y := by
  unfold tauOp
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib, mul_sub]

lemma tauOp_smul (c : ℝ) (Y : (EE D r s) →L[ℂ] (EE D r s)) :
    (tauOp (c • Y)).re = c * (tauOp Y).re := by
  have : c • Y = (c : ℂ) • Y := (Complex.coe_smul c Y).symm
  rw [this]
  unfold tauOp
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum]
  rw [mul_left_comm, Complex.re_ofReal_mul]

lemma re_tauOp_mono (Y Z : (EE D r s) →L[ℂ] (EE D r s)) (h : Y ≤ Z) :
    (tauOp Y).re ≤ (tauOp Z).re := by
  have := re_tauOp_nonneg (Z - Y) (sub_nonneg.mpr h)
  rw [tauOp_sub, Complex.sub_re] at this
  linarith

lemma re_tauOp_star_mul_self (F : (EE D r s) →L[ℂ] (EE D r s)) :
    (tauOp (star F * F)).re = (D : ℝ)⁻¹ * ∑ a : Fin D, ‖F (vv D r s a)‖ ^ 2 := by
  rw [tauOp_re]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-! ### The faithfulness argument -/

/-- The cut-off `f(x) = max 0 (min 1 ((x - (M - ε)) / ε))`. -/
def cut (M ε : ℝ) (x : ℝ) : ℝ := max 0 (min 1 ((x - (M - ε)) / ε))

lemma continuous_cut (M ε : ℝ) : Continuous (cut M ε) := by
  unfold cut; fun_prop

lemma cut_nonneg (M ε x : ℝ) : 0 ≤ cut M ε x := le_max_left _ _

lemma cut_le_one (M ε x : ℝ) : cut M ε x ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma cut_eq_zero (M ε x : ℝ) (hε : 0 < ε) (hx : x ≤ M - ε) : cut M ε x = 0 := by
  unfold cut
  apply le_antisymm _ (le_max_left _ _)
  apply max_le le_rfl
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma cut_self (M ε : ℝ) (hε : 0 < ε) : cut M ε M = 1 := by
  unfold cut
  rw [sub_sub_cancel, div_self hε.ne', min_self, max_eq_right zero_le_one]

theorem exists_cut {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (T : A) (hT : 0 ≤ T) (hpos : 0 < ‖T‖) (ε : ℝ) (hε : 0 < ε) (_hεM : ε < ‖T‖) :
    ∃ F : A, F ≠ 0 ∧ (∀ b, Commute T b → Commute F b) ∧
      ∀ p : ℕ, (‖T‖ - ε) ^ p • (star F * F) ≤ T ^ p := by
  classical
  set M := ‖T‖ with hM
  have hTsa : IsSelfAdjoint T := hT.isSelfAdjoint
  have : Nontrivial A := nontrivial_of_ne T 0 (norm_pos_iff.mp hpos)
  have hcont := (continuous_cut M ε).continuousOn (s := spectrum ℝ T)
  set F := cfc (cut M ε) T with hF
  have hFsa : IsSelfAdjoint F := cfc_predicate _ _
  have hMspec : M ∈ spectrum ℝ T := CStarAlgebra.norm_mem_spectrum_of_nonneg hT
  have hF0 : F ≠ 0 := by
    intro h0
    have h0' : cfc (cut M ε) T = cfc (fun _ : ℝ => (0 : ℝ)) T := by
      rw [← hF, h0]; exact (cfc_zero ℝ T).symm
    have := eqOn_of_cfc_eq_cfc h0' (hf := hcont) (hg := continuousOn_const) (ha := hTsa) hMspec
    simp only [cut_self M ε hε] at this
    exact one_ne_zero this
  refine ⟨F, hF0, fun b hb => hb.cfc_real _, fun p => ?_⟩
  have hspec : ∀ x ∈ spectrum ℝ T, 0 ≤ x ∧ x ≤ M := by
    intro x hx
    refine ⟨spectrum_nonneg_of_nonneg hT hx, ?_⟩
    exact (Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx)
  have h1 : star F * F = cfc (fun x => cut M ε x * cut M ε x) T := by
    rw [hFsa.star_eq, hF, cfc_mul _ _ T]
  have h2 : T ^ p = cfc (fun x : ℝ => x ^ p) T := (cfc_pow_id T p).symm
  rw [h1, h2, ← cfc_smul .., cfc_le_iff _ _ T]
  intro x hx
  obtain ⟨hx0, hxM⟩ := hspec x hx
  simp only [smul_eq_mul]
  by_cases hxε : x ≤ M - ε
  · rw [cut_eq_zero M ε x hε hxε]; simp; positivity
  · push_neg at hxε
    have hff : cut M ε x * cut M ε x ≤ 1 := by
      nlinarith [cut_nonneg M ε x, cut_le_one M ε x]
    calc (M - ε) ^ p * (cut M ε x * cut M ε x) ≤ (M - ε) ^ p * 1 := by
          gcongr
      _ ≤ x ^ p := by rw [mul_one]; exact pow_le_pow_left₀ (by linarith) hxε.le p

theorem exists_lower (T : (EE D r s) →L[ℂ] (EE D r s)) (hT : 0 ≤ T)
    (hU : ∀ g : G r s, Commute T (U D g)) (hpos : 0 < ‖T‖)
    (ε : ℝ) (hε : 0 < ε) (hεM : ε < ‖T‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, c * (‖T‖ - ε) ^ p ≤ (tauOp (T ^ p)).re := by
  classical
  obtain ⟨F, hF0, hFc, hle⟩ := exists_cut T hT hpos ε hε hεM
  have hFU : ∀ g, Commute F (U D g) := fun g => hFc _ (hU g)
  set c := (tauOp (star F * F)).re with hc
  have hcpos : 0 < c := by
    rw [hc, re_tauOp_star_mul_self]
    by_contra hle'
    push_neg at hle'
    have hsum : ∑ a : Fin D, ‖F (vv D r s a)‖ ^ 2 ≤ 0 := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · subst hD; simp
      · have : (0 : ℝ) < (D : ℝ)⁻¹ := by positivity
        by_contra h'
        push_neg at h'
        have := mul_pos this h'
        linarith
    have hzero : ∀ a, F (vv D r s a) = 0 := by
      intro a
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => sq_nonneg ‖F (vv D r s a)‖)).mp
        (le_antisymm hsum (Finset.sum_nonneg fun a _ => sq_nonneg _)) a (Finset.mem_univ a)
      simpa using h1
    apply hF0
    apply eq_zero_of_single_delta
    intro a g
    have : (PiLp.single 2 a (delta g) : EE D r s) = U D g⁻¹ (vv D r s a) := by
      rw [vv, U_single, rightReg_delta_one]
    rw [this, ← ContinuousLinearMap.mul_apply, (hFU g⁻¹).eq, ContinuousLinearMap.mul_apply,
      hzero, map_zero]
  refine ⟨c, hcpos, fun p => ?_⟩
  have h1 := re_tauOp_mono _ _ (hle p)
  have e : (tauOp ((‖T‖ - ε) ^ p • (star F * F))).re = (‖T‖ - ε) ^ p * c := tauOp_smul _ _
  have h2 : (‖T‖ - ε) ^ p * c ≤ (tauOp (T ^ p)).re := e ▸ h1
  linarith [h2]

lemma norm_star_mul_self_gen {A : Type*} [CStarAlgebra A] (x : A) :
    ‖star x * x‖ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self

theorem tendsto_gen (B T : (EE D r s) →L[ℂ] (EE D r s)) (hTdef : T = star B * B)
    (hTU : ∀ g, Commute T (U D g)) (hD0 : D = 0 → B = 0) :
    Tendsto (fun p : ℕ => (tauOp (T ^ p)).re ^ (1 / (2 * (p : ℝ)))) atTop (𝓝 ‖B‖) := by
  have hT : 0 ≤ T := by rw [hTdef]; exact star_mul_self_nonneg B
  have hTn : ‖T‖ = ‖B‖ * ‖B‖ := by rw [hTdef]; exact norm_star_mul_self_gen B
  have hnn : ∀ p : ℕ, 0 ≤ (tauOp (T ^ p)).re := fun p =>
    re_tauOp_nonneg _ (CStarAlgebra.pow_nonneg hT p)
  -- upper bound
  have hup : ∀ p : ℕ, 1 ≤ p → (tauOp (T ^ p)).re ^ (1 / (2 * (p : ℝ))) ≤ ‖B‖ := by
    intro p hp
    have h1 : (tauOp (T ^ p)).re ≤ ‖B‖ ^ (2 * p) := by
      calc (tauOp (T ^ p)).re ≤ ‖T ^ p‖ := re_tauOp_le_norm _
        _ ≤ ‖T‖ ^ p := norm_pow_le' _ (by omega)
        _ = ‖B‖ ^ (2 * p) := by rw [hTn, pow_mul, sq]
    have h2 : (1 / (2 * (p : ℝ))) = ((2 * p : ℕ) : ℝ)⁻¹ := by push_cast; ring
    calc (tauOp (T ^ p)).re ^ (1 / (2 * (p : ℝ))) ≤ (‖B‖ ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) :=
          Real.rpow_le_rpow (hnn p) h1 (by positivity)
      _ = ‖B‖ := by rw [h2, Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)]
  rw [tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Eventually.of_forall fun p => lt_of_lt_of_le ha0 (Real.rpow_nonneg (hnn p) _)
    push_neg at ha0
    have hBpos : 0 < ‖B‖ := lt_of_le_of_lt ha0 ha
    have hTpos : 0 < ‖T‖ := by rw [hTn]; positivity
    have hD : D ≠ 0 := by
      intro hD
      have := hD0 hD
      rw [this, norm_zero] at hBpos
      exact lt_irrefl _ hBpos
    set M := ‖T‖
    have ha2 : a ^ 2 < M := by rw [hTn]; nlinarith
    set ε := (M - a ^ 2) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hεM : ε < M := by rw [hε]; nlinarith [sq_nonneg a]
    obtain ⟨c, hc, hlow⟩ := exists_lower T hT hTU hTpos ε hε0 hεM
    have hMε : 0 < M - ε := by linarith
    have has : a < Real.sqrt (M - ε) := by
      rw [Real.lt_sqrt ha0]; rw [hε]; linarith
    -- `c ^ (1/(2p)) → 1`
    have hexp : Tendsto (fun p : ℕ => 1 / (2 * (p : ℝ))) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (two_pos : (0:ℝ) < 2)
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp this
    have hcl : Tendsto (fun p : ℕ => c ^ (1 / (2 * (p : ℝ))) * Real.sqrt (M - ε)) atTop
        (𝓝 (Real.sqrt (M - ε))) := by
      have h1 : Tendsto (fun p : ℕ => c ^ (1 / (2 * (p : ℝ)))) atTop (𝓝 (c ^ (0 : ℝ))) :=
        ((Real.continuousAt_const_rpow hc.ne').tendsto).comp hexp
      rw [Real.rpow_zero] at h1
      simpa using h1.mul_const (Real.sqrt (M - ε))
    filter_upwards [hcl.eventually (lt_mem_nhds has), eventually_ge_atTop 1] with p hp hp1
    refine lt_of_lt_of_le hp ?_
    have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    have hpos' : (0 : ℝ) < 2 * p := by linarith
    calc c ^ (1 / (2 * (p : ℝ))) * Real.sqrt (M - ε)
        = (c * (M - ε) ^ p) ^ (1 / (2 * (p : ℝ))) := by
          rw [Real.mul_rpow hc.le (pow_nonneg hMε.le _), Real.sqrt_eq_rpow,
            ← Real.rpow_natCast, ← Real.rpow_mul hMε.le]
          congr 2
          field_simp
      _ ≤ (tauOp (T ^ p)).re ^ (1 / (2 * (p : ℝ))) :=
          Real.rpow_le_rpow (by positivity) (hlow p) (by positivity)
  · intro b hb
    filter_upwards [eventually_ge_atTop 1] with p hp
    exact lt_of_le_of_lt (hup p hp) hb

/-! ### Back to the group algebra -/

lemma regOp_mul (x y : MG D r s) : regOp (x * y) = regOp x * regOp y :=
  opOf_mul (lregHom r s) x y

lemma regOp_one : regOp (1 : MG D r s) = 1 := opOf_one (lregHom r s)

lemma regOp_pow (x : MG D r s) (p : ℕ) : regOp (x ^ p) = regOp x ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero, regOp_one]
  | succ k ih => rw [pow_succ, pow_succ, regOp_mul, ih]

lemma regOp_adj (x : MG D r s) : regOp (adj x) = star (regOp x) :=
  (opOf_adj (fun g : G r s => DerandSq.leftReg g) star_leftReg x).symm

lemma regOp_adj_mul_pow (x : MG D r s) (p : ℕ) :
    regOp ((adj x * x) ^ p) = (star (regOp x) * regOp x) ^ p := by
  rw [regOp_pow, regOp_mul, regOp_adj]

/-- Faithfulness of the trace: moments of `x*x` recover the norm. -/
theorem faithful {D : ℕ} (hD : 1 ≤ D) (x : MG D r s) :
    Tendsto (fun p : ℕ => ((trTau ((adj x * x) ^ p)).re) ^ (1 / (2 * (p : ℝ)))) atTop
      (𝓝 ‖regOp x‖) := by
  have h := tendsto_gen (regOp x) (star (regOp x) * regOp x) rfl
    (fun g => by
      have := commute_regOp_U (adj x * x) g
      rwa [regOp_mul, regOp_adj] at this)
    (fun h0 => by omega)
  refine h.congr fun p => ?_
  rw [trTau_eq_tauOp, regOp_adj_mul_pow]

end BordenaveCollins.PartL

end
end

section
open Filter Topology
open BordenaveCollins

theorem solution {r s : ℕ} {D : ℕ} (hD : 1 ≤ D) (x : MG D r s) :
    Tendsto (fun p : ℕ => ((trTau ((adj x * x) ^ p)).re) ^ (1 / (2 * (p : ℝ)))) atTop
      (𝓝 ‖regOp x‖) :=
  BordenaveCollins.PartL.faithful hD x

end
