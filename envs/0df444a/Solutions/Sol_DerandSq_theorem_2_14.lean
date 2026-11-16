-- Prove2me | solution 1 for DerandSq.theorem_2_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:20:43.997394+00:00
-- url     : https://prove2.me/submissions/3799880a-ce79-4f52-a229-8f92b26ba47e

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_DerandSq_NCPoly_eval
import Definitions.Def_DerandSq_permOp
import Definitions.Def_DerandSq_perpCompress
import Theorems.Thm_BordenaveCollins_exists_tail_le_of_rational_moments
import Theorems.Thm_BordenaveCollins_exists_expFix_eq_rational
import Theorems.Thm_BordenaveCollins_exists_linearization
import Theorems.Thm_BordenaveCollins_norm_sum_cfun_mul_trace_Bprod_le
import Theorems.Thm_BordenaveCollins_tendsto_expFix
import Theorems.Thm_BordenaveCollins_tendsto_re_trTau_pow_rpow

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

/-! ## Colourings of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPerm ω (u.drop t) y`). -/

/-! ## Matrix coefficients -/

/-- `x` in the permutation representation of a sample, on `D` copies of `ℂ^N`. -/
def modelOp {D r s N : ℕ} (ω : Om r s N) (x : MG D r s) :=
  opOf (fun g : G r s => DerandSq.permOp (act ω g)) x

/-- `x` in the permutation representation, compressed to `1^⊥`. -/
def perpOp {D r s N : ℕ} (ω : Om r s N) (x : MG D r s) :=
  DerandSq.perpCompress D N (modelOp ω x)

/-- The expected spectral functional of the compressed model at size `N`:
`E[(1/(DN)) Re Tr f(Y_ω)]`, `Y_ω = perpOp ω x`, with `f(Y)` the continuous functional calculus. -/
def specE (D r s N : ℕ) (x : MG D r s) (f : ℝ → ℝ) : ℝ :=
  (∑ ω : Om r s N, (LinearMap.trace ℂ _
      ((cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (perpOp ω x) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)))).re) /
    ((Fintype.card (Om r s N) : ℝ) * ((D : ℝ) * N))

end BordenaveCollins

end

/-! ## Definitions of the bridge and crude bounds -/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

/-- A crude bound for the norm of `x` in any unitary representation. -/
def bnd {D : ℕ} (x : MG D r s) : ℝ := ∑ g ∈ x.coeff.support, ∑ a, ∑ b, ‖x.coeff g a b‖

/-- The largest word length in the support. -/
def lenmax {D : ℕ} (x : MG D r s) : ℕ := x.coeff.support.sup len

/-- The group element of a letter `x_i`, `y_j` (`Sum.inl`) or `x_i*`, `y_j*` (`Sum.inr`). -/
def letterG : (Fin r ⊕ Fin s) ⊕ (Fin r ⊕ Fin s) → G r s
  | Sum.inl (Sum.inl i) => Monoid.Coprod.inl (FreeGroup.of i)
  | Sum.inl (Sum.inr j) => Monoid.Coprod.inr (DerandSq.mGen j)
  | Sum.inr (Sum.inl i) => (Monoid.Coprod.inl (FreeGroup.of i))⁻¹
  | Sum.inr (Sum.inr j) => Monoid.Coprod.inr (DerandSq.mGen j)

/-- The group element of a word. -/
def wordG (w : FreeMonoid ((Fin r ⊕ Fin s) ⊕ (Fin r ⊕ Fin s))) : G r s :=
  (w.toList.map letterG).prod

/-- A polynomial as an element of the matrix-coefficient group algebra. -/
def toAlg {D : ℕ} (P : DerandSq.NCPoly D (Fin r ⊕ Fin s)) : MG D r s :=
  P.sum fun w A => MonoidAlgebra.single (wordG w) A

end BordenaveCollins

end
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

theorem tensorOp_one_one {n : ℕ} :
    tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  refine op_ext _ _ fun x a => ?_
  simp [tensorOp_apply, Matrix.one_apply]

theorem norm_inject_apply {n : ℕ} (i : Fin n) (y : H) :
    ‖(inject i : H →L[ℂ] Composite (Fin n) H) y‖ = ‖y‖ := by
  simp [inject]

theorem norm_tensorOp_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    ‖tensorOp A T‖ ≤ (∑ a, ∑ b, ‖A a b‖) * ‖T‖ := by
  have key : ∀ i j : Fin n,
      ‖(inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
        Composite (Fin n) H →L[ℂ] Composite (Fin n) H)‖ ≤ ‖A i j‖ * ‖T‖ := by
    intro i j
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      fun x => ?_
    have h1 : ‖(inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
        Composite (Fin n) H →L[ℂ] Composite (Fin n) H) x‖ = ‖A i j • T (x j)‖ := by
      rw [← norm_inject_apply (n := n) i (A i j • T (x j))]
      rfl
    rw [h1, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _))) (norm_nonneg _)
  have e : tensorOp A T = ∑ i, ∑ j, (inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
        Composite (Fin n) H →L[ℂ] Composite (Fin n) H) := rfl
  rw [e, Finset.sum_mul]
  refine norm_sum_le_of_le (E := Composite (Fin n) H →L[ℂ] Composite (Fin n) H) Finset.univ
    fun i _ => ?_
  rw [Finset.sum_mul]
  exact norm_sum_le_of_le (E := Composite (Fin n) H →L[ℂ] Composite (Fin n) H) Finset.univ
    fun j _ => key i j

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

/-- A self-adjoint idempotent has norm at most one. -/
theorem norm_le_one_of_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : E →L[ℂ] E) (h1 : P * P = P) (h2 : star P = P) : ‖P‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  have e : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right P, ← ContinuousLinearMap.star_eq_adjoint, h2,
      ← mul_apply_eq_comp, h1]
  have h : ‖P x‖ * ‖P x‖ ≤ ‖x‖ * ‖P x‖ := by
    have := re_inner_le_norm (𝕜 := ℂ) x (P x)
    rw [← e, inner_self_eq_norm_sq_to_K] at this
    have h3 : (((‖P x‖ : ℝ) : ℂ) ^ 2).re = ‖P x‖ * ‖P x‖ := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re, sq]
    simpa [h3] using this
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg (P x), norm_nonneg x]

end Tensor

/-! ## Trace of a tensor operator -/

section Trace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem trace_tensorOp_term {n : ℕ} (a b : Fin n) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin n => H))
      ((inject a ∘L T ∘L PiLp.proj 2 (fun _ : Fin n => H) b :
        PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      if a = b then LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) else 0 := by
  set S : H →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H) :=
    ((inject a : H →L[ℂ] PiLp 2 (fun _ : Fin n => H)) : H →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H))
    with hS
  set F : PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] H :=
    ((T.comp (PiLp.proj 2 (fun _ : Fin n => H) b) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] H) :
      PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] H) with hF
  have h1 : ((inject a ∘L T ∘L PiLp.proj 2 (fun _ : Fin n => H) b :
        PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) = S ∘ₗ F := by
    ext x : 1
    simp [hS, hF]
  rw [h1, LinearMap.trace_comp_comm' F S]
  by_cases hab : a = b
  · subst hab
    have : F ∘ₗ S = (T : H →ₗ[ℂ] H) := by
      ext y : 1
      simp [hS, hF, inject]
    rw [this, if_pos rfl]
  · have : F ∘ₗ S = 0 := by
      ext y : 1
      simp [hS, hF, inject, Ne.symm hab]
    rw [this, if_neg hab, map_zero]

theorem trace_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin n => H))
      ((tensorOp A T : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      A.trace * LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  have hterm : ∀ i j : Fin n, (inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
      PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      A i j • (inject i ∘L T ∘L PiLp.proj 2 (fun _ : Fin n => H) j) := by
    intro i j
    ext x : 1
    simp
  unfold tensorOp
  simp only [hterm, ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
    map_sum, map_smul, trace_tensorOp_term, smul_eq_mul]
  simp [Matrix.trace, Finset.sum_mul, mul_ite, Finset.sum_ite_eq]

end Trace

/-! ## Permutation operators -/

section Perm
open DerandSq

theorem permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N))
    (j : Fin N) : permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

theorem permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

theorem permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

theorem norm_permOp_le {N : ℕ} (π : Equiv.Perm (Fin N)) : ‖permOp π‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact le_of_eq (LinearIsometryEquiv.norm_map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ π) x)

theorem inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    inner ℂ (permOp π x) y = inner ℂ x (permOp π⁻¹ y) := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem star_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) : star (permOp π) = permOp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_permOp, inv_inv]

/-- The model representation as a monoid homomorphism into operators. -/
def permHom {r s N : ℕ} (ω : Om r s N) :
    G r s →* (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) where
  toFun g := permOp (act ω g)
  map_one' := by rw [map_one, permOp_one]
  map_mul' g h := by rw [map_mul, permOp_mul]

theorem permHom_apply {r s N : ℕ} (ω : Om r s N) (g : G r s) :
    permHom ω g = permOp (act ω g) := rfl

end Perm

/-! ## The left regular representation -/

section Reg
open DerandSq

theorem leftReg_apply {Γ : Type*} [Group Γ] (g : Γ) (f : L2 Γ) (h : Γ) :
    leftReg g f h = f (g⁻¹ * h) := rfl

theorem leftReg_mul {Γ : Type*} [Group Γ] (g h : Γ) :
    leftReg (g * h) = leftReg g * leftReg h := by
  ext f k
  simp [leftReg_apply, mul_assoc]

theorem leftReg_one {Γ : Type*} [Group Γ] : leftReg (1 : Γ) = 1 := by
  ext f k
  simp [leftReg_apply]

/-- The left regular representation as a monoid homomorphism into operators. -/
def regHom (Γ : Type*) [Group Γ] : Γ →* (L2 Γ →L[ℂ] L2 Γ) where
  toFun g := leftReg g
  map_one' := leftReg_one
  map_mul' := leftReg_mul

end Reg

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

/-- `1 - J` on `ℂ^N`. -/
def Qn (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ)))

/-- `1 ⊗ (1 - J)` on `D` copies of `ℂ^N`. -/
def QQ (D N : ℕ) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) :=
  tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) (Qn N)

theorem Qn_apply {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    Qn N x i = x i - (N : ℂ)⁻¹ * ∑ j, x j := by
  show (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ))) x).ofLp i = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    Matrix.one_apply]

theorem Qn_mul_self (N : ℕ) : Qn N * Qn N = Qn N := by
  ext x i
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact i.elim0
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mul_apply_eq_comp, Qn_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem star_Qn (N : ℕ) : star (Qn N) = Qn N := by
  unfold Qn
  rw [← map_star]
  congr 1
  ext i j
  simp [Matrix.one_apply, eq_comm]

theorem Qn_permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) : Qn N * permOp σ = permOp σ * Qn N := by
  ext x i
  simp only [mul_apply_eq_comp, Qn_apply, permOp_apply]
  congr 2
  exact Equiv.sum_comp σ.symm (fun j => x j)

theorem QQ_mul_self (D N : ℕ) : QQ D N * QQ D N = QQ D N := by
  unfold QQ
  rw [tensorOp_mul, Qn_mul_self, mul_one]

theorem star_QQ (D N : ℕ) : star (QQ D N) = QQ D N := by
  unfold QQ
  rw [star_tensorOp, star_Qn, Matrix.conjTranspose_one]

theorem norm_QQ_le (D N : ℕ) : ‖QQ D N‖ ≤ 1 :=
  norm_le_one_of_proj _ (QQ_mul_self D N) (star_QQ D N)

theorem QQ_tensorOp_permOp {D N : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin N)) :
    QQ D N * tensorOp A (permOp σ) = tensorOp A (permOp σ) * QQ D N := by
  unfold QQ
  rw [tensorOp_mul, tensorOp_mul, Qn_permOp, one_mul, mul_one]

/-- `Tr(P_σ (1 - J)) = fix σ - 1`. -/
theorem trace_permOp_Qn {N : ℕ} (hN : 1 ≤ N) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp σ * Qn N :
      EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount σ : ℂ) - 1 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, mul_apply_eq_comp, permOp_apply, Qn_apply]
  rw [Finset.sum_sub_distrib, fixCount, Finset.card_filter, Nat.cast_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have : (σ.symm i = i) ↔ (σ i = i) := by
      rw [Equiv.symm_apply_eq, eq_comm]
    by_cases h : σ i = i
    · simp [h, this.mpr h]
    · simp [h, mt this.mp h]
  · simp [hN']

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

theorem opOf_pow (π : G r s →* (H →L[ℂ] H)) (x : MG D r s) (p : ℕ) :
    opOf (fun g => π g) (x ^ p) = opOf (fun g => π g) x ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero, opOf_one']
  | succ p ih => rw [pow_succ, pow_succ, opOf_mul', ih]

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

/-- Operators on `D` copies of `ℂ^N`. -/
abbrev Op (D N : ℕ) := PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))

theorem modelOp_eq {D N : ℕ} (ω : Om r s N) (x : MG D r s) :
    modelOp ω x = opOf (fun g => permHom ω g) x := rfl

theorem perpOp_eq {D N : ℕ} (ω : Om r s N) (x : MG D r s) :
    perpOp ω x = QQ D N * (modelOp ω x * QQ D N) := rfl

theorem modelOp_mul {D N : ℕ} (ω : Om r s N) (x y : MG D r s) :
    modelOp ω (x * y) = modelOp ω x * modelOp ω y := by
  rw [modelOp_eq, modelOp_eq, modelOp_eq, opOf_mul']

theorem star_modelOp {D N : ℕ} (ω : Om r s N) (x : MG D r s) :
    star (modelOp ω x) = modelOp ω (adj x) :=
  opOf_adj' _ (fun g => by
    show star (permOp (act ω g)) = permOp (act ω g⁻¹)
    rw [star_permOp, (act ω).map_inv g]) x

theorem QQ_modelOp {D N : ℕ} (ω : Om r s N) (x : MG D r s) :
    QQ D N * modelOp ω x = modelOp ω x * QQ D N := by
  unfold modelOp opOf
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun g _ => QQ_tensorOp_permOp _ _

theorem norm_modelOp_le {D N : ℕ} (ω : Om r s N) (x : MG D r s) : ‖modelOp ω x‖ ≤ bnd x := by
  unfold modelOp opOf bnd
  refine norm_sum_le_of_le (E := Op D N) _ fun g _ => ?_
  refine (norm_tensorOp_le _ _).trans ?_
  exact mul_le_of_le_one_right
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (norm_permOp_le _)

theorem norm_perpOp_le {D N : ℕ} (ω : Om r s N) (x : MG D r s) : ‖perpOp ω x‖ ≤ bnd x := by
  rw [perpOp_eq]
  have h1 : ‖(modelOp ω x * QQ D N : Op D N)‖ ≤ bnd x := by
    refine (norm_mul_le (α := Op D N) _ _).trans ?_
    calc ‖modelOp ω x‖ * ‖QQ D N‖ ≤ bnd x * 1 :=
          mul_le_mul (norm_modelOp_le ω x) (norm_QQ_le D N) (norm_nonneg _)
            ((norm_nonneg _).trans (norm_modelOp_le ω x))
      _ = bnd x := mul_one _
  refine (norm_mul_le (α := Op D N) _ _).trans ?_
  calc ‖QQ D N‖ * ‖(modelOp ω x * QQ D N : Op D N)‖ ≤ 1 * bnd x :=
        mul_le_mul (norm_QQ_le D N) h1 (norm_nonneg _) zero_le_one
    _ = bnd x := one_mul _

/-- The compression is multiplicative on the model operators. -/
theorem perpOp_mul {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (x y : MG D r s) :
    perpOp ω (x * y) = perpOp ω x * perpOp ω y := by
  rw [perpOp_eq, perpOp_eq, perpOp_eq, modelOp_mul]
  have hy := QQ_modelOp ω y
  symm
  calc QQ D N * (modelOp ω x * QQ D N) * (QQ D N * (modelOp ω y * QQ D N))
      = QQ D N * modelOp ω x * (QQ D N * QQ D N) * (modelOp ω y * QQ D N) := by
        simp only [mul_assoc]
    _ = QQ D N * modelOp ω x * (QQ D N * modelOp ω y) * QQ D N := by
        rw [QQ_mul_self]; simp only [mul_assoc]
    _ = QQ D N * modelOp ω x * (modelOp ω y * QQ D N) * QQ D N := by rw [hy]
    _ = QQ D N * (modelOp ω x * modelOp ω y * QQ D N) := by
        simp only [mul_assoc]; rw [QQ_mul_self]

theorem star_perpOp {D N : ℕ} (ω : Om r s N) (x : MG D r s) :
    star (perpOp ω x) = perpOp ω (adj x) := by
  rw [perpOp_eq, perpOp_eq, star_mul, star_mul, star_QQ, star_modelOp, mul_assoc]

/-- The trace of the compressed model operator, in terms of fixed points. -/
theorem trace_perpOp {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (y : MG D r s) :
    LinearMap.trace ℂ _ ((perpOp ω y :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) =
      ∑ g ∈ y.coeff.support, Matrix.trace (y.coeff g) * ((fixCount (act ω g) : ℂ) - 1) := by
  have h1 : ((perpOp ω y : Op D N) :
      PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) =
      ((QQ D N : Op D N) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) *
        ((modelOp ω y * QQ D N : Op D N) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) := rfl
  have h2 : ((modelOp ω y * QQ D N : Op D N) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) *
      ((QQ D N : Op D N) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) =
      ((modelOp ω y * QQ D N * QQ D N : Op D N) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) := rfl
  have h3 : (modelOp ω y * QQ D N * QQ D N : Op D N) =
      ∑ g ∈ y.coeff.support, tensorOp (y.coeff g) (permOp (act ω g) * Qn N) := by
    rw [mul_assoc, QQ_mul_self]
    unfold modelOp opOf QQ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [tensorOp_mul, mul_one]
  rw [h1, LinearMap.trace_mul_comm, h2, h3]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum, trace_tensorOp, trace_permOp_Qn hN]

/-! ## The trace `τ` -/

/-- `e_b ⊗ δ_1`. -/
def dvec (D r s : ℕ) (b : Fin D) : PiLp 2 (fun _ : Fin D => L2 (G r s)) :=
  inject b (lp.single 2 (1 : G r s) (1 : ℂ))

theorem norm_dvec {D : ℕ} (b : Fin D) : ‖dvec D r s b‖ = 1 := by
  unfold dvec
  rw [norm_inject_apply, lp.norm_single (by norm_num)]
  simp

/-- The coefficient at the identity as a matrix entry of the regular representation. -/
theorem regOp_dvec {D : ℕ} (y : MG D r s) (a b : Fin D) :
    (regOp y (dvec D r s b)) a (1 : G r s) = y.coeff 1 a b := by
  have h : ∀ g : G r s, ((tensorOp (y.coeff g) (leftReg g)) (dvec D r s b)) a (1 : G r s) =
      if g = 1 then y.coeff g a b else 0 := by
    intro g
    rw [tensorOp_apply]
    have hv : ∀ b' : Fin D, (dvec D r s b) b' =
        if b' = b then lp.single 2 (1 : G r s) (1 : ℂ) else 0 := by
      intro b'
      simp [dvec, inject]
    simp only [hv, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
    rw [Finset.sum_eq_single b]
    · simp [leftReg_apply, lp.single_apply, Pi.single_apply]
    · intro b' _ hb'
      simp [hb']
    · simp
  unfold regOp opOf
  rw [_root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, lp.coeFn_sum,
    Finset.sum_apply]
  simp only [h]
  rw [Finset.sum_ite_eq']
  split_ifs with h1
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h1]; rfl

theorem norm_trTau_le {D : ℕ} (y : MG D r s) : ‖trTau y‖ ≤ ‖regOp y‖ := by
  have hentry : ∀ a : Fin D, ‖y.coeff 1 a a‖ ≤ ‖regOp y‖ := by
    intro a
    rw [← regOp_dvec y a a]
    calc ‖(regOp y (dvec D r s a)) a (1 : G r s)‖ ≤ ‖(regOp y (dvec D r s a)) a‖ :=
          lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖regOp y (dvec D r s a)‖ := PiLp.norm_apply_le _ a
      _ ≤ ‖regOp y‖ * ‖dvec D r s a‖ := (regOp y).le_opNorm _
      _ = ‖regOp y‖ := by rw [norm_dvec, mul_one]
  unfold trTau
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have : ‖Matrix.trace (y.coeff 1)‖ ≤ D * ‖regOp y‖ := by
    unfold Matrix.trace
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => hentry a).trans ?_
    simp
  rw [inv_mul_le_iff₀ hD']
  exact this

theorem regOp_pow {D : ℕ} (z : MG D r s) (p : ℕ) : regOp (z ^ p) = regOp z ^ p :=
  opOf_pow (regHom (G r s)) z p

theorem norm_pow_le_op {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : E →L[ℂ] E)
    (p : ℕ) : ‖X ^ p‖ ≤ ‖X‖ ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ p ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

theorem trTau_pow_le {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (p : ℕ) :
    ‖trTau (z ^ p)‖ ≤ ‖regOp z‖ ^ p := by
  refine (norm_trTau_le (z ^ p)).trans ?_
  rw [regOp_pow]
  exact norm_pow_le_op _ p

/-! ## Word length of the support of a polynomial -/

theorem len_one : len (1 : G r s) = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl ⟨[], rfl, by simp [wprod]⟩)

theorem len_mul_le (g h : G r s) : len (g * h) ≤ len g + len h := by
  obtain ⟨nf, -, h2, -, h4⟩ := nf_exists r s
  rw [h4 g, h4 h]
  refine Nat.sInf_le ⟨nf g ++ nf h, List.length_append, ?_⟩
  rw [wprod, List.map_append, List.prod_append]
  exact congrArg₂ (· * ·) (h2 g) (h2 h)

theorem len_support_pow {D : ℕ} (z : MG D r s) (k : ℕ) (g : G r s)
    (hg : g ∈ (z ^ k).coeff.support) : len g ≤ k * lenmax z := by
  induction k generalizing g with
  | zero =>
    have := MonoidAlgebra.support_coeff_one_subset (by rwa [pow_zero] at hg)
    rw [Finset.mem_one] at this
    rw [this, len_one]; simp
  | succ k ih =>
    rw [pow_succ] at hg
    have := MonoidAlgebra.support_coeff_mul_subset _ _ hg
    obtain ⟨g₁, h₁, g₂, h₂, rfl⟩ := Finset.mem_mul.mp this
    have hb : len g₂ ≤ lenmax z := Finset.le_sup (f := len) h₂
    calc len (g₁ * g₂) ≤ len g₁ + len g₂ := len_mul_le _ _
      _ ≤ k * lenmax z + lenmax z := add_le_add (ih g₁ h₁) hb
      _ = (k + 1) * lenmax z := by ring

theorem len_support_aeval {D : ℕ} (z : MG D r s) (h : ℝ[X]) (g : G r s)
    (hg : g ∈ (Polynomial.aeval z h).coeff.support) : len g ≤ h.natDegree * lenmax z := by
  rw [Polynomial.aeval_eq_sum_range, MonoidAlgebra.coeff_sum] at hg
  have := Finsupp.support_finsetSum hg
  obtain ⟨k, hk, hgk⟩ := Finset.mem_biUnion.mp this
  rw [MonoidAlgebra.coeff_smul] at hgk
  have hgk' := Finsupp.support_smul hgk
  have hk' : k ≤ h.natDegree := by
    have := Finset.mem_range.mp hk
    omega
  exact (len_support_pow z k g hgk').trans (Nat.mul_le_mul_right _ hk')

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

theorem norm_perpOp_le {D N : ℕ} (ω : Om r s N) (x : MG D r s) : ‖perpOp ω x‖ ≤ bnd x :=
  PartO1.norm_perpOp_le ω x

theorem len_support_aeval {D : ℕ} (z : MG D r s) (h : ℝ[X]) (g : G r s)
    (hg : g ∈ (Polynomial.aeval z h).coeff.support) : len g ≤ h.natDegree * lenmax z :=
  PartO1.len_support_aeval z h g hg

theorem trTau_pow_le {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (p : ℕ) :
    ‖trTau (z ^ p)‖ ≤ ‖regOp z‖ ^ p :=
  PartO1.trTau_pow_le hD z p

/-- The trace of the compressed model operator, in terms of fixed points. -/
theorem trace_perpOp {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (y : MG D r s) :
    LinearMap.trace ℂ _ ((perpOp ω y :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) =
      ∑ g ∈ y.coeff.support, Matrix.trace (y.coeff g) * ((fixCount (act ω g) : ℂ) - 1) :=
  PartO1.trace_perpOp hN ω y

/-- The compression is multiplicative on the model operators. -/
theorem perpOp_mul {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (x y : MG D r s) :
    perpOp ω (x * y) = perpOp ω x * perpOp ω y :=
  PartO1.perpOp_mul hN ω x y

theorem star_perpOp {D N : ℕ} (ω : Om r s N) (x : MG D r s) :
    star (perpOp ω x) = perpOp ω (adj x) :=
  PartO1.star_perpOp ω x

end BordenaveCollins

end
end

section
/-!
# The statements proved in Part A, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem abstract_tail (K : ℝ) (hK : 0 < K) (c : ℕ) (hc : 1 ≤ c) (E : ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ n f g, E n (f + g) = E n f + E n g)
    (hsmul : ∀ n (a : ℝ) f, E n (a • f) = a * E n f)
    (hmono : ∀ n f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E n f ≤ E n g)
    (hone : ∀ n, E n (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ n : ℕ, C * q ≤ n →
          E n (fun x => h.eval x) =
            f.eval (1 / ((c : ℝ) * n)) / gq.eval (1 / ((c : ℝ) * n)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : ℕ → ℝ)
    (ha : ∀ p : ℕ, Tendsto (fun n : ℕ => E n (fun x => x ^ p)) atTop (𝓝 (a p)))
    (hb : ∀ p : ℕ, Tendsto (fun n : ℕ => ((c : ℝ) * n) * (E n (fun x => x ^ p) - a p)) atTop
      (𝓝 (b p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hbgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |b p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      E n (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤ C / (n : ℝ) ^ 2 :=
  BordenaveCollins.exists_tail_le_of_rational_moments K hK c hc E hadd hsmul hmono hone hrat ρ hρ a b ha hb hagrow hbgrow ε hε

end BordenaveCollins

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

theorem rational (r s q : ℕ) (hq : 1 ≤ q) :
    ∃ gq : ℝ[X], gq.natDegree ≤ (r + s) * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / (4 * ((r : ℝ) + s + 1) * (q : ℝ) ^ 2)),
        1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ g : G r s, len g ≤ q → ∃ f : ℝ[X], f.natDegree ≤ (r + s + 2) * q ∧
        ∀ N : ℕ, Adm s N → q ≤ N →
          expFix r s N g = N * (f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ))) :=
  BordenaveCollins.exists_expFix_eq_rational r s q hq

end BordenaveCollins

end
end

section
/-!
# Part O2: the spectral functional `specE`

Linearity, positivity, mass, polynomial moments and the Markov tail bound for `specE`.
-/

open Finset Polynomial

noncomputable section

namespace BordenaveCollins.PartO2

set_option linter.unusedSectionVars false

open scoped ComplexOrder

variable {r s : ℕ}

/-! ## Generic facts on a finite-dimensional Hilbert space -/

section Gen

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- A real function applied to an operator (complex functional calculus of `w ↦ f (re w)`). -/
def fc (f : ℝ → ℝ) (Y : V →L[ℂ] V) : V →L[ℂ] V :=
  cfc (fun w : ℂ => ((f w.re : ℝ) : ℂ)) Y

/-- The trace as a linear functional on bounded operators. -/
def trL : (V →L[ℂ] V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ V) ∘ₗ (ContinuousLinearMap.coeLM ℂ)

/-- The real part of the trace. -/
def trR (T : V →L[ℂ] V) : ℝ := (trL T).re

lemma trR_def (T : V →L[ℂ] V) :
    trR T = (LinearMap.trace ℂ V (T : V →ₗ[ℂ] V)).re := rfl

lemma trR_add (A B : V →L[ℂ] V) : trR (A + B) = trR A + trR B := by
  unfold trR; rw [map_add, Complex.add_re]

lemma trR_sub (A B : V →L[ℂ] V) : trR (A - B) = trR A - trR B := by
  unfold trR; rw [map_sub, Complex.sub_re]

lemma trR_smul (c : ℝ) (A : V →L[ℂ] V) : trR ((c : ℂ) • A) = c * trR A := by
  unfold trR; rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma trL_one : trL (1 : V →L[ℂ] V) = (Module.finrank ℂ V : ℂ) := by
  show LinearMap.trace ℂ V (1 : V →ₗ[ℂ] V) = _
  exact LinearMap.trace_one ℂ V

lemma contOn (Y : V →L[ℂ] V) (F : ℂ → ℂ) : ContinuousOn F (spectrum ℂ Y) := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact (Module.End.finite_spectrum _).continuousOn F

lemma fc_add (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (f g : ℝ → ℝ) :
    fc (f + g) Y = fc f Y + fc g Y := by
  have := hY.isStarNormal
  unfold fc
  rw [← cfc_add (a := Y) (fun w : ℂ => ((f w.re : ℝ) : ℂ)) (fun w : ℂ => ((g w.re : ℝ) : ℂ))
    (contOn Y _) (contOn Y _)]
  apply cfc_congr
  intro w _
  simp

lemma fc_smul (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (a : ℝ) (f : ℝ → ℝ) :
    fc (a • f) Y = (a : ℂ) • fc f Y := by
  have := hY.isStarNormal
  unfold fc
  rw [← cfc_const_mul (a : ℂ) (fun w : ℂ => ((f w.re : ℝ) : ℂ)) Y (contOn Y _)]
  apply cfc_congr
  intro w _
  simp

lemma mem_spec (Y : V →L[ℂ] V) (_hY : IsSelfAdjoint Y) {K : ℝ} (hK : ‖Y‖ ≤ K) {w : ℂ}
    (hw : w ∈ spectrum ℂ Y) : w.re ∈ Set.Icc (-K) K := by
  rcases subsingleton_or_nontrivial (V →L[ℂ] V) with hA | hA
  · exact absurd hw (by rw [spectrum.of_subsingleton]; exact Set.notMem_empty _)
  have hn : ‖w‖ ≤ ‖Y‖ := spectrum.norm_le_norm_of_mem hw
  have h1 : |w.re| ≤ K := (Complex.abs_re_le_norm w).trans (hn.trans hK)
  exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩

lemma fc_mono (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) {K : ℝ} (hK : ‖Y‖ ≤ K) (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ Set.Icc (-K) K, f x ≤ g x) : fc f Y ≤ fc g Y := by
  unfold fc
  refine cfc_mono (fun w hw => ?_) (contOn Y _) (contOn Y _)
  exact Complex.real_le_real.mpr (hfg _ (mem_spec Y hY hK hw))

lemma trR_nonneg (T : V →L[ℂ] V) (hT : 0 ≤ T) : 0 ≤ trR T := by
  have hp : (T : V →ₗ[ℂ] V).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff T).mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT)
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

lemma trR_fc_mono (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) {K : ℝ} (hK : ‖Y‖ ≤ K) (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ Set.Icc (-K) K, f x ≤ g x) : trR (fc f Y) ≤ trR (fc g Y) := by
  have h := trR_nonneg _ (sub_nonneg.mpr (fc_mono Y hY hK f g hfg))
  rw [trR_sub] at h
  linarith

lemma fc_const_one (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) : fc (fun _ => 1) Y = 1 := by
  have := hY.isStarNormal
  unfold fc
  simpa using cfc_const_one ℂ Y

lemma fc_nonneg (Y : V →L[ℂ] V) (f : ℝ → ℝ) (h0 : ∀ x, 0 ≤ f x) : 0 ≤ fc f Y := by
  unfold fc
  exact cfc_nonneg (fun x _ => Complex.zero_le_real.mpr (h0 _))

lemma fc_poly (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (h : ℝ[X]) :
    fc (fun x => h.eval x) Y =
      ∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • Y ^ k := by
  have := hY.isStarNormal
  unfold fc
  have : cfc (fun z : ℂ => ((h.eval z.re : ℝ) : ℂ)) Y =
      cfc (fun z : ℂ => (h.map (algebraMap ℝ ℂ)).eval z) Y := by
    apply cfc_congr
    intro z hz
    have := hY.mem_spectrum_eq_re hz
    simp only
    conv_rhs => rw [this]
    simp [Polynomial.eval_map, ← Complex.coe_algebraMap, Polynomial.eval₂_at_apply]
  rw [this, cfc_polynomial (h.map (algebraMap ℝ ℂ)) Y, aeval_eq_sum_range, natDegree_map]
  simp [coeff_map]

/-- If `c ≤ ‖Y‖` then the spectral projection of `{|x| ≥ c}` has trace at least one. -/
lemma trR_ge_one [Nontrivial V] (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (c : ℝ)
    (hcY : c ≤ ‖Y‖) : 1 ≤ trR (fc (fun t => if c ≤ |t| then 1 else 0) Y) := by
  have := hY.isStarNormal
  set χ : ℝ → ℝ := fun t => if c ≤ |t| then 1 else 0 with hχ
  have h0 : ∀ x, 0 ≤ χ x := fun x => by simp only [hχ]; split_ifs <;> norm_num
  obtain ⟨l, hl, hn⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty Y)
  rw [hY.spectralRadius_eq_nnnorm] at hn
  have hnorm : ‖l‖ = ‖Y‖ := by
    have := congrArg ENNReal.toReal hn
    simpa using this
  have hre : (l.re : ℂ) = l := (hY.mem_spectrum_eq_re hl).symm
  have habs : c ≤ |l.re| := by
    have h2 : ‖l‖ = |l.re| := by
      conv_lhs => rw [← hre]
      exact Complex.norm_real _
    linarith
  set T := fc χ Y with hTdef
  have hT0 : 0 ≤ T := fc_nonneg Y χ h0
  have hmem : (1 : ℂ) ∈ spectrum ℂ T := by
    rw [hTdef, fc, cfc_map_spectrum (hf := contOn Y _) _ Y]
    exact ⟨l, hl, by simp [hχ, habs]⟩
  have hp : (T : V →ₗ[ℂ] V).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff T).mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT0)
  rw [ContinuousLinearMap.spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hmem
  obtain ⟨i, hi⟩ := hp.isSymmetric.exists_eigenvalues_eq rfl hmem
  rw [trR_def, ← RCLike.re_to_complex, hp.isSymmetric.re_trace_eq_sum_eigenvalues rfl]
  calc (1:ℝ) = hp.isSymmetric.eigenvalues rfl i := (Complex.ofReal_eq_one.mp hi).symm
    _ ≤ _ := Finset.single_le_sum (fun j _ => hp.nonneg_eigenvalues rfl j) (Finset.mem_univ i)

end Gen

/-! ## The model space -/

lemma finrank_space (D N : ℕ) :
    Module.finrank ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) = D * N := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin D → EuclideanSpace ℂ (Fin N))).finrank_eq,
    Module.finrank_pi_fintype]
  simp

lemma nontrivial_space {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) :
    Nontrivial (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) := by
  apply Module.nontrivial_of_finrank_pos (R := ℂ)
  rw [finrank_space]
  positivity

lemma specE_eq (D N : ℕ) (z : MG D r s) (f : ℝ → ℝ) :
    specE D r s N z f = (∑ ω : Om r s N, trR (fc f (perpOp ω z))) /
      ((Fintype.card (Om r s N) : ℝ) * ((D : ℝ) * N)) := rfl

lemma sa {D N : ℕ} (z : MG D r s) (hz : adj z = z) (ω : Om r s N) :
    IsSelfAdjoint (perpOp ω z) := by
  unfold IsSelfAdjoint
  rw [star_perpOp, hz]

/-! ## Linearity, positivity, mass -/

theorem specE_add {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) (f g : ℝ → ℝ) :
    specE D r s N z (f + g) = specE D r s N z f + specE D r s N z g := by
  rw [specE_eq, specE_eq, specE_eq, ← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [fc_add _ (sa z hz ω), trR_add]

theorem specE_smul {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) (a : ℝ) (f : ℝ → ℝ) :
    specE D r s N z (a • f) = a * specE D r s N z f := by
  rw [specE_eq, specE_eq, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [fc_smul _ (sa z hz ω), trR_smul]

theorem specE_mono {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ Set.Icc (-(bnd z)) (bnd z), f x ≤ g x) :
    specE D r s N z f ≤ specE D r s N z g := by
  rw [specE_eq, specE_eq]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => ?_) (by positivity)
  exact trR_fc_mono _ (sa z hz ω) (norm_perpOp_le ω z) f g hfg

theorem specE_one_le {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) :
    specE D r s N z (fun _ => 1) ≤ 1 := by
  rw [specE_eq]
  have h : ∀ ω : Om r s N, trR (fc (fun _ => 1) (perpOp ω z)) = (D : ℝ) * N := by
    intro ω
    rw [fc_const_one _ (sa z hz ω), trR, trL_one, finrank_space]
    simp
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact div_self_le_one _

/-! ## Polynomial moments -/

/-- `y ↦ ∑_g tr(y_g) c_g`. -/
def Lf {D : ℕ} (c : G r s → ℂ) (y : MG D r s) : ℂ :=
  ∑ g ∈ y.coeff.support, Matrix.trace (y.coeff g) * c g

lemma Lf_eq {D : ℕ} (c : G r s → ℂ) (y : MG D r s) :
    Lf c y = y.coeff.sum fun g A => Matrix.trace A * c g := rfl

/-- `Lf` as a real-linear map. -/
def LfL {D : ℕ} (c : G r s → ℂ) : MG D r s →ₗ[ℝ] ℂ where
  toFun := Lf c
  map_add' x y := by
    rw [Lf_eq, Lf_eq, Lf_eq, MonoidAlgebra.coeff_add]
    exact Finsupp.sum_add_index' (by simp) (by intro g A B; simp [add_mul])
  map_smul' a y := by
    rw [Lf_eq, Lf_eq, MonoidAlgebra.coeff_smul, Finsupp.sum_smul_index' (by simp)]
    simp only [Finsupp.sum, Matrix.trace_smul, RingHom.id_apply, Finset.smul_sum, smul_mul_assoc]

lemma Lf_one {D : ℕ} (c : G r s → ℂ) : Lf c (1 : MG D r s) = (D : ℂ) * c 1 := by
  rw [Lf_eq, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
    Finsupp.sum_single_index (by simp)]
  simp

lemma Lf_re {D N : ℕ} (ω : Om r s N) (y : MG D r s) :
    (Lf (fun g => (fixCount (act ω g) : ℂ) - 1) y).re =
      ∑ g ∈ y.coeff.support, (Matrix.trace (y.coeff g)).re * ((fixCount (act ω g) : ℝ) - 1) := by
  unfold Lf
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [Complex.mul_re]

lemma perpOp_pow {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (z : MG D r s) (k : ℕ) :
    (perpOp ω z) ^ (k + 1) = perpOp ω (z ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ z (k + 1), perpOp_mul hN]

lemma trL_pow {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (z : MG D r s) (k : ℕ) :
    trL ((perpOp ω z) ^ k) =
      Lf (fun g => (fixCount (act ω g) : ℂ) - 1) (z ^ k) + if k = 0 then (D : ℂ) else 0 := by
  cases k with
  | zero =>
    rw [pow_zero, pow_zero, trL_one, finrank_space, Lf_one]
    have : fixCount (act ω (1 : G r s)) = N := by simp [fixCount]
    rw [this, if_pos rfl]
    push_cast
    ring
  | succ k =>
    rw [perpOp_pow hN]
    simp only [Nat.succ_ne_zero, if_false, add_zero]
    exact trace_perpOp hN ω (z ^ (k + 1))

lemma trR_poly {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (z : MG D r s) (hz : adj z = z)
    (h : ℝ[X]) :
    trR (fc (fun t => h.eval t) (perpOp ω z)) =
      ∑ g ∈ (Polynomial.aeval z h).coeff.support,
        (Matrix.trace ((Polynomial.aeval z h).coeff g)).re * ((fixCount (act ω g) : ℝ) - 1) +
      (D : ℝ) * h.eval 0 := by
  rw [← Lf_re, fc_poly _ (sa z hz ω), trR, map_sum]
  simp only [map_smul, trL_pow hN, smul_add, Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.range (h.natDegree + 1),
      (h.coeff k : ℂ) • (if k = 0 then (D : ℂ) else 0) = ((D : ℝ) * h.eval 0 : ℝ) := by
    rw [Finset.sum_eq_single 0 (by intro b _ hb; simp [hb]) (by simp)]
    simp [Polynomial.coeff_zero_eq_eval_zero, mul_comm]
  have h2 : ∑ k ∈ Finset.range (h.natDegree + 1),
      (h.coeff k : ℂ) • Lf (fun g => (fixCount (act ω g) : ℂ) - 1) (z ^ k) =
      Lf (fun g => (fixCount (act ω g) : ℂ) - 1) (Polynomial.aeval z h) := by
    show _ = LfL (fun g => (fixCount (act ω g) : ℂ) - 1) (Polynomial.aeval z h)
    rw [aeval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    simp [LfL]
  rw [h1, h2, Complex.add_re, Complex.ofReal_re]

lemma pm_nonempty {N : ℕ} (hN : Even N) : Nonempty (DerandSq.PM N) := by
  obtain ⟨k, rfl⟩ := hN
  let σ : Equiv.Perm (Fin (k + k)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)
  refine ⟨⟨σ, fun x => ⟨?_, ?_⟩⟩⟩
  · simp [σ]
  · intro hx
    have h2 : (finSumFinEquiv.symm x).swap = finSumFinEquiv.symm x := by
      apply finSumFinEquiv.injective
      simpa [σ] using hx
    cases h : finSumFinEquiv.symm x <;> rw [h] at h2 <;> simp at h2

lemma om_nonempty {N : ℕ} (hA : Adm s N) : Nonempty (Om r s N) := by
  have : Nonempty (Fin s → DerandSq.PM N) := by
    rcases hA with rfl | hA
    · exact ⟨fun j => j.elim0⟩
    · have := pm_nonempty hA
      infer_instance
  infer_instance

/-- The spectral functional of a polynomial, in terms of expected fixed points. -/
theorem specE_poly {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (N : ℕ) (hN : 1 ≤ N)
    (hA : Adm s N) (h : ℝ[X]) :
    specE D r s N z (fun t => h.eval t) =
      (∑ g ∈ (Polynomial.aeval z h).coeff.support,
          (Matrix.trace ((Polynomial.aeval z h).coeff g)).re * (expFix r s N g - 1)) /
        ((D : ℝ) * N) + h.eval 0 / N := by
  have := om_nonempty (r := r) hA
  have hcard : (0 : ℝ) < Fintype.card (Om r s N) := by exact_mod_cast Fintype.card_pos
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [specE_eq]
  simp only [trR_poly hN _ z hz h]
  have hE : ∀ g : G r s, ∑ ω : Om r s N, ((fixCount (act ω g) : ℝ) - 1) =
      (Fintype.card (Om r s N) : ℝ) * (expFix r s N g - 1) := by
    intro g
    unfold expFix
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [← Finset.mul_sum, hE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : ∑ g ∈ (Polynomial.aeval z h).coeff.support,
      (Matrix.trace ((Polynomial.aeval z h).coeff g)).re *
        ((Fintype.card (Om r s N) : ℝ) * (expFix r s N g - 1)) =
      (Fintype.card (Om r s N) : ℝ) * ∑ g ∈ (Polynomial.aeval z h).coeff.support,
        (Matrix.trace ((Polynomial.aeval z h).coeff g)).re * (expFix r s N g - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  rw [this]
  field_simp

/-! ## The tail bound -/

theorem tail_le {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (N : ℕ) (hN : 1 ≤ N)
    (ρ' : ℝ) :
    PunctSketch.coinProb (fun ω : Om r s N => ρ' ≤ ‖perpOp ω z‖) ≤
      (D : ℝ) * N * specE D r s N z (fun t => if ρ' ≤ |t| then 1 else 0) := by
  classical
  have := nontrivial_space hD hN
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hrhs : (D : ℝ) * N * specE D r s N z (fun t => if ρ' ≤ |t| then 1 else 0) =
      (∑ ω : Om r s N, trR (fc (fun t => if ρ' ≤ |t| then 1 else 0) (perpOp ω z))) /
        (Fintype.card (Om r s N) : ℝ) := by
    rw [specE_eq]
    field_simp
  rw [hrhs]
  unfold PunctSketch.coinProb
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hcard : ((Finset.univ.filter fun ω : Om r s N => ρ' ≤ ‖perpOp ω z‖).card : ℝ) =
      ∑ ω : Om r s N, if ρ' ≤ ‖perpOp ω z‖ then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  convert (Finset.sum_le_sum fun (ω : Om r s N) _ => ?_ :
    (∑ ω : Om r s N, if ρ' ≤ ‖perpOp ω z‖ then (1 : ℝ) else 0) ≤ _) using 1
  split_ifs with hω
  · exact trR_ge_one _ (sa z hz ω) ρ' hω
  · exact trR_nonneg _ (fc_nonneg _ _ fun x => by split_ifs <;> norm_num)

end BordenaveCollins.PartO2

end
end

section
/-!
# The statements proved in Part O2, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem specE_add {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) (f g : ℝ → ℝ) :
    specE D r s N z (f + g) = specE D r s N z f + specE D r s N z g :=
  PartO2.specE_add z hz N f g

theorem specE_smul {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) (a : ℝ) (f : ℝ → ℝ) :
    specE D r s N z (a • f) = a * specE D r s N z f :=
  PartO2.specE_smul z hz N a f

theorem specE_mono {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ Set.Icc (-(bnd z)) (bnd z), f x ≤ g x) :
    specE D r s N z f ≤ specE D r s N z g :=
  PartO2.specE_mono z hz N f g hfg

theorem specE_one_le {D : ℕ} (z : MG D r s) (hz : adj z = z) (N : ℕ) :
    specE D r s N z (fun _ => 1) ≤ 1 :=
  PartO2.specE_one_le z hz N

/-- The spectral functional of a polynomial, in terms of expected fixed points. -/
theorem specE_poly {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (N : ℕ) (hN : 1 ≤ N)
    (hA : Adm s N) (h : ℝ[X]) :
    specE D r s N z (fun t => h.eval t) =
      (∑ g ∈ (Polynomial.aeval z h).coeff.support,
          (Matrix.trace ((Polynomial.aeval z h).coeff g)).re * (expFix r s N g - 1)) /
        ((D : ℝ) * N) + h.eval 0 / N :=
  PartO2.specE_poly hD z hz N hN hA h

theorem tail_le {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (N : ℕ) (hN : 1 ≤ N)
    (ρ' : ℝ) :
    PunctSketch.coinProb (fun ω : Om r s N => ρ' ≤ ‖perpOp ω z‖) ≤
      (D : ℝ) * N * specE D r s N z (fun t => if ρ' ≤ |t| then 1 else 0) :=
  PartO2.tail_le hD z hz N hN ρ'

end BordenaveCollins

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

theorem nu_one_bound {D : ℕ} (x : MG D r s) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (C : ℝ) (k : ℕ), ∀ p : ℕ, 1 ≤ p →
      ‖∑ g ∈ (x ^ p).coeff.support,
          if g = 1 then (0 : ℂ) else (cfun g : ℂ) * Matrix.trace ((x ^ p).coeff g)‖ ≤
        C * (p : ℝ) ^ k * (‖regOp x‖ + δ) ^ p := by
  obtain ⟨L, hX, htr⟩ := BordenaveCollins.exists_linearization x δ hδ
  have hc0 : 0 < ‖regOp x‖ + δ := by positivity
  have hR0 : 0 ≤ (‖regOp x‖ + δ) ^ (1 / (L.q : ℝ)) := Real.rpow_nonneg hc0.le _
  have hRq : ((‖regOp x‖ + δ) ^ (1 / (L.q : ℝ))) ^ L.q = ‖regOp x‖ + δ := by
    rw [one_div, Real.rpow_inv_natCast_pow hc0.le (by have := L.hq; omega)]
  obtain ⟨C, k, hC⟩ := BordenaveCollins.norm_sum_cfun_mul_trace_Bprod_le L _ hR0 hX
  refine ⟨C * (L.q : ℝ) ^ k, k, fun p hp => ?_⟩
  have hm : 1 ≤ p * L.q := Nat.mul_pos hp L.hq
  set F : G r s → ℂ := fun g =>
    if g = 1 then (0 : ℂ) else (cfun g : ℂ) * Matrix.trace ((x ^ p).coeff g) with hFdef
  set h : (Fin (p * L.q) → Option (Lt r s)) → ℂ := fun i =>
    if iprod i = 1 then (0 : ℂ) else (cfun (iprod i) : ℂ) * (Bprod L (p * L.q) i).trace
    with hhdef
  have hF : ∀ g, F g = ∑ i with iprod i = g, h i := by
    intro g
    by_cases hg : g = 1
    · have h0 : F g = 0 := by simp only [hFdef, if_pos hg]
      rw [h0]
      symm
      refine Finset.sum_eq_zero fun i hi => ?_
      have : iprod i = 1 := (Finset.mem_filter.mp hi).2.trans hg
      simp only [hhdef, if_pos this]
    · have h0 : F g = (cfun g : ℂ) * Matrix.trace ((x ^ p).coeff g) := by
        simp only [hFdef, if_neg hg]
      rw [h0, htr p hp g, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : iprod i = g
      · have hi1 : ¬ iprod i = 1 := fun h' => hg (hi.symm.trans h')
        simp only [hhdef, if_pos hi, if_neg hi1]
        rw [hi]
      · simp only [if_neg hi, mul_zero]
  have key : ∑ g ∈ (x ^ p).coeff.support, F g = ∑ i, h i := by
    set S : Finset (G r s) := (x ^ p).coeff.support ∪ Finset.univ.image iprod with hS
    calc ∑ g ∈ (x ^ p).coeff.support, F g = ∑ g ∈ S, F g := by
          refine Finset.sum_subset Finset.subset_union_left fun g _ hg => ?_
          have h0 : (x ^ p).coeff g = 0 := Finsupp.notMem_support_iff.mp hg
          simp only [hFdef, h0, Matrix.trace_zero, mul_zero, ite_self]
      _ = ∑ g ∈ S, ∑ i with iprod i = g, h i := Finset.sum_congr rfl fun g _ => hF g
      _ = ∑ i, h i :=
          Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_univ i))) h
  rw [key]
  refine (hC (p * L.q) hm).trans (le_of_eq ?_)
  rw [pow_mul', hRq]
  push_cast
  ring

end BordenaveCollins.PartP1

end
end

section
/-!
# The statements proved in Part P1, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem nu_one_bound {D : ℕ} (x : MG D r s) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (C : ℝ) (k : ℕ), ∀ p : ℕ, 1 ≤ p →
      ‖∑ g ∈ (x ^ p).coeff.support,
          if g = 1 then (0 : ℂ) else (cfun g : ℂ) * Matrix.trace ((x ^ p).coeff g)‖ ≤
        C * (p : ℝ) ^ k * (‖regOp x‖ + δ) ^ p :=
  PartP1.nu_one_bound x δ hδ

end BordenaveCollins

end
end

section
/-!
# Part U: the upper tail (assembly)

`upper_tail` from `abstract_tail`, the `specE_*` stubs, `tail_le`, `rational`, `tendsto_expFix`,
`nu_one_bound`, `trTau_pow_le` and `len_support_aeval`.
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartU

variable {r s : ℕ}

/-! ## Small facts about the model -/

theorem stp_pos (s : ℕ) : 1 ≤ stp s := by
  unfold stp; split_ifs <;> norm_num

theorem adm (s n : ℕ) : Adm s (stp s * n) := by
  unfold Adm stp
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr (even_two_mul n)

/-- A fixed-point-free involution of `Fin (2 * n)`. -/
theorem pm_nonempty (n : ℕ) : Nonempty (DerandSq.PM (2 * n)) := by
  let e : Fin 2 × Fin n ≃ Fin (2 * n) := finProdFinEquiv
  refine ⟨⟨e.symm.trans ((Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)).trans e),
    fun x => ?_⟩⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective x
  constructor
  · simp
  · intro h
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.refl_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_true] at h
    fin_cases a <;> simp at h

theorem om_nonempty (r s n : ℕ) : Nonempty (Om r s (stp s * n)) := by
  by_cases h : s = 0
  · subst h
    exact ⟨(fun _ => 1, fun j => j.elim0)⟩
  · have h2 : stp s = 2 := by simp [stp, h]
    rw [h2]
    obtain ⟨σ⟩ := pm_nonempty n
    exact ⟨(fun _ => 1, fun _ => σ)⟩

theorem expFix_one (r s n : ℕ) :
    expFix r s (stp s * n) (1 : G r s) = ((stp s * n : ℕ) : ℝ) := by
  have := om_nonempty r s n
  unfold expFix
  have h : ∀ ω : Om r s (stp s * n), (fixCount (act ω 1) : ℝ) = ((stp s * n : ℕ) : ℝ) := by
    intro ω
    simp [fixCount]
  have hc : (Fintype.card (Om r s (stp s * n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-! ## The limits `a p`, `b p` -/

/-- The zeroth-order moments. -/
def aa {D : ℕ} (z : MG D r s) (p : ℕ) : ℝ := (trTau (z ^ p)).re

/-- The first-order sum. -/
def SS {D : ℕ} (z : MG D r s) (p : ℕ) : ℝ :=
  ∑ g ∈ (z ^ p).coeff.support,
    if g = 1 then 0 else (Matrix.trace ((z ^ p).coeff g)).re * (cfun g : ℝ)

/-- The first-order moments. -/
def bb {D : ℕ} (z : MG D r s) (p : ℕ) : ℝ :=
  SS z p / D - aa z p + (if p = 0 then 1 else 0)

theorem aa_eq {D : ℕ} (z : MG D r s) (p : ℕ) :
    aa z p = (Matrix.trace ((z ^ p).coeff 1)).re / D := by
  unfold aa trTau
  have : ((D : ℂ))⁻¹ = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  ring

theorem moment_formula {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (n : ℕ)
    (hn : 1 ≤ n) (p : ℕ) :
    ((stp s : ℝ) * n) * (specE D r s (stp s * n) z (fun x => x ^ p) - aa z p) =
      (∑ g ∈ (z ^ p).coeff.support, if g = 1 then 0 else
          (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1)) / D
        - aa z p + (if p = 0 then 1 else 0) := by
  have hs := stp_pos s
  have hN : 1 ≤ stp s * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hfun : (fun x : ℝ => x ^ p) = fun t => (X ^ p : ℝ[X]).eval t := by
    funext t; simp
  have haev : Polynomial.aeval z (X ^ p : ℝ[X]) = z ^ p := by simp
  rw [hfun, specE_poly hD z hz _ hN (adm s n) (X ^ p), haev]
  have hsplit : ∑ g ∈ (z ^ p).coeff.support,
        (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1) =
      (Matrix.trace ((z ^ p).coeff 1)).re * (((stp s * n : ℕ) : ℝ) - 1) +
        ∑ g ∈ (z ^ p).coeff.support, if g = 1 then 0 else
          (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1) := by
    have h1 : ∀ g ∈ (z ^ p).coeff.support,
        (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1) =
          (if g = 1 then
              (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1) else 0) +
            (if g = 1 then 0 else
              (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1)) := by
      intro g _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq']
    congr 1
    split_ifs with h1s
    · rw [expFix_one]
    · have : (z ^ p).coeff 1 = 0 := Finsupp.notMem_support_iff.mp h1s
      simp [this]
  have h0 : (X ^ p : ℝ[X]).eval 0 = if p = 0 then 1 else 0 := by
    simp [zero_pow_eq]
  rw [hsplit, aa_eq, h0]
  generalize (∑ g ∈ (z ^ p).coeff.support, if g = 1 then 0 else
          (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1)) = S
  generalize (if p = 0 then (1 : ℝ) else 0) = i0
  generalize (Matrix.trace ((z ^ p).coeff 1)).re = T
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have hs' : (stp s : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem tendsto_cn (s : ℕ) : Tendsto (fun n : ℕ => (stp s : ℝ) * n) atTop atTop := by
  have hs := stp_pos s
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)

theorem hb {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (p : ℕ) :
    Tendsto (fun n : ℕ => ((stp s : ℝ) * n) *
      (specE D r s (stp s * n) z (fun x => x ^ p) - aa z p)) atTop (𝓝 (bb z p)) := by
  have hlim : Tendsto (fun n : ℕ =>
      (∑ g ∈ (z ^ p).coeff.support, if g = 1 then 0 else
          (Matrix.trace ((z ^ p).coeff g)).re * (expFix r s (stp s * n) g - 1)) / D
        - aa z p + (if p = 0 then 1 else 0)) atTop (𝓝 (bb z p)) := by
    unfold bb SS
    refine Tendsto.add (Tendsto.sub (Tendsto.div_const ?_ _) tendsto_const_nhds)
      tendsto_const_nhds
    refine tendsto_finsetSum _ fun g _ => ?_
    by_cases hg : g = 1
    · simp only [hg, if_true]; exact tendsto_const_nhds
    · simp only [hg, if_false]
      refine Tendsto.const_mul _ ?_
      have := (tendsto_expFix g hg).sub_const 1
      simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (moment_formula hD z hz n hn p).symm

theorem ha {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (p : ℕ) :
    Tendsto (fun n : ℕ => specE D r s (stp s * n) z (fun x => x ^ p)) atTop (𝓝 (aa z p)) := by
  have h1 := (hb hD z hz p).div_atTop (tendsto_cn s)
  have h2 := h1.const_add (aa z p)
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs := stp_pos s
  have hs' : (stp s : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ## Growth -/

theorem abs_aa_le {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (p : ℕ) :
    |aa z p| ≤ ‖regOp z‖ ^ p :=
  (Complex.abs_re_le_norm _).trans (trTau_pow_le hD z p)

theorem SS_eq_re {D : ℕ} (z : MG D r s) (p : ℕ) :
    SS z p = (∑ g ∈ (z ^ p).coeff.support,
      if g = 1 then (0 : ℂ) else (cfun g : ℂ) * Matrix.trace ((z ^ p).coeff g)).re := by
  unfold SS
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs
  · simp
  · simp [mul_comm]

theorem pow_mul_bdd (k : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∃ M : ℝ, ∀ p : ℕ, (p : ℝ) ^ k * θ ^ p ≤ M := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (r := θ)
    (by rw [abs_of_nonneg h0]; exact h1)
  obtain ⟨M, hM⟩ := h.bddAbove_range
  exact ⟨M, fun p => hM ⟨p, rfl⟩⟩

theorem hbgrow {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ p : ℕ, |bb z p| ≤ C * (‖regOp z‖ + δ) ^ p := by
  set ρ := ‖regOp z‖ with hρdef
  have hρ : 0 ≤ ρ := norm_nonneg _
  obtain ⟨C, k, hC⟩ := nu_one_bound z (δ / 2) (by positivity)
  have hpos : 0 < ρ + δ := by positivity
  obtain ⟨M, hM⟩ := pow_mul_bdd k ((ρ + δ / 2) / (ρ + δ)) (by positivity)
    (by rw [div_lt_one hpos]; linarith)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  refine ⟨|C| * M + 1 + |bb z 0|, fun p => ?_⟩
  have hpp : 0 ≤ (ρ + δ) ^ p := by positivity
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : 0 ≤ |C| * M := by positivity
    simp only [pow_zero, mul_one]
    linarith
  · have hS : |SS z p| ≤ |C| * M * (ρ + δ) ^ p := by
      rw [SS_eq_re]
      refine (Complex.abs_re_le_norm _).trans ((hC p hp).trans ?_)
      have hθ : (ρ + δ / 2) ^ p = ((ρ + δ / 2) / (ρ + δ)) ^ p * (ρ + δ) ^ p := by
        rw [← mul_pow, div_mul_cancel₀ _ hpos.ne']
      rw [hθ]
      have h1 : (p : ℝ) ^ k * ((ρ + δ / 2) / (ρ + δ)) ^ p ≤ M := hM p
      have h2 : 0 ≤ (p : ℝ) ^ k * ((ρ + δ / 2) / (ρ + δ)) ^ p := by positivity
      calc C * (p : ℝ) ^ k * (((ρ + δ / 2) / (ρ + δ)) ^ p * (ρ + δ) ^ p)
          = C * ((p : ℝ) ^ k * ((ρ + δ / 2) / (ρ + δ)) ^ p) * (ρ + δ) ^ p := by ring
        _ ≤ |C| * M * (ρ + δ) ^ p := by
            refine mul_le_mul_of_nonneg_right ?_ hpp
            exact (mul_le_mul_of_nonneg_right (le_abs_self C) h2).trans
              (mul_le_mul_of_nonneg_left h1 (abs_nonneg C))
    have hSD : |SS z p / D| ≤ |SS z p| := by
      rw [abs_div, Nat.abs_cast]
      exact div_le_self (abs_nonneg _) (by exact_mod_cast hD)
    have hA : |aa z p| ≤ (ρ + δ) ^ p :=
      (abs_aa_le hD z p).trans (pow_le_pow_left₀ hρ (by linarith) p)
    have hb0 : 0 ≤ |bb z 0| * (ρ + δ) ^ p := by positivity
    have hbb : bb z p = SS z p / D - aa z p := by
      unfold bb; simp [hp.ne']
    rw [hbb]
    calc |SS z p / D - aa z p| ≤ |SS z p / D| + |aa z p| := abs_sub _ _
      _ ≤ |C| * M * (ρ + δ) ^ p + (ρ + δ) ^ p := add_le_add (hSD.trans hS) hA
      _ ≤ (|C| * M + 1 + |bb z 0|) * (ρ + δ) ^ p := by nlinarith

/-! ## Rationality -/

theorem hrat {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) :
    ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ n : ℕ, C * q ≤ n →
          specE D r s (stp s * n) z (fun x => h.eval x) =
            f.eval (1 / (((stp s : ℕ) : ℝ) * n)) / gq.eval (1 / (((stp s : ℕ) : ℝ) * n)) := by
  set L := lenmax z with hL
  set A := (L + 1) ^ 2 with hA
  have hLA : L + 1 ≤ A := Nat.le_self_pow (by norm_num) _
  refine ⟨4 * (r + s + 3) * A + 1, fun q hq => ?_⟩
  have hq' : 1 ≤ q * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨gq, hdeg, hint, hf⟩ := rational r s (q * (L + 1)) hq'
  have hqA : q * (L + 1) ≤ q * A := Nat.mul_le_mul_left _ hLA
  have hbig : (r + s + 2) * (q * (L + 1)) ≤ (4 * (r + s + 3) * A + 1) * q := by
    calc (r + s + 2) * (q * (L + 1)) ≤ (r + s + 3) * (q * A) :=
          Nat.mul_le_mul (by omega) hqA
      _ ≤ (4 * (r + s + 3) * A + 1) * q := by nlinarith [Nat.zero_le ((r + s + 3) * (q * A))]
  have hq'C : q * (L + 1) ≤ (4 * (r + s + 3) * A + 1) * q :=
    le_trans (Nat.le_mul_of_pos_left _ (by omega)) hbig
  refine ⟨gq, ?_, ?_, ?_⟩
  · exact le_trans hdeg (le_trans (Nat.mul_le_mul_right _ (by omega)) hbig)
  · intro x hx
    refine hint x ⟨hx.1, hx.2.trans ?_⟩
    have hnat : 4 * (r + s + 1) * (q * (L + 1)) ^ 2 ≤ (4 * (r + s + 3) * A + 1) * q ^ 2 := by
      have e : 4 * (r + s + 1) * (q * (L + 1)) ^ 2 = (4 * (r + s + 1) * A) * q ^ 2 := by
        rw [hA]; ring
      rw [e]
      refine Nat.mul_le_mul_right _ ?_
      have : 4 * (r + s + 1) * A ≤ 4 * (r + s + 3) * A :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hreal : 4 * ((r : ℝ) + s + 1) * ((q * (L + 1) : ℕ) : ℝ) ^ 2 ≤
        ((4 * (r + s + 3) * A + 1 : ℕ) : ℝ) * (q : ℝ) ^ 2 := by
      exact_mod_cast hnat
    have hqpos : (0 : ℝ) < ((q * (L + 1) : ℕ) : ℝ) := by exact_mod_cast hq'
    exact one_div_le_one_div_of_le (by positivity) hreal
  · intro h hh
    set y := Polynomial.aeval z h with hy
    have hlen : ∀ g ∈ y.coeff.support, len g ≤ q * (L + 1) := by
      intro g hg
      calc len g ≤ h.natDegree * L := len_support_aeval z h g hg
        _ ≤ q * (L + 1) := Nat.mul_le_mul hh (by omega)
    have hex : ∀ g : G r s, ∃ f : ℝ[X], len g ≤ q * (L + 1) →
        (f.natDegree ≤ (r + s + 2) * (q * (L + 1)) ∧
          ∀ N : ℕ, Adm s N → q * (L + 1) ≤ N →
            expFix r s N g = N * (f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)))) := by
      intro g
      by_cases hg : len g ≤ q * (L + 1)
      · obtain ⟨f, hf1, hf2⟩ := hf g hg
        exact ⟨f, fun _ => ⟨hf1, hf2⟩⟩
      · exact ⟨0, fun h' => absurd h' hg⟩
    choose f hfg using hex
    have hlen1 : len (1 : G r s) ≤ q * (L + 1) := by
      have h0 : len (1 : G r s) = 0 := by
        unfold len
        apply Nat.eq_zero_of_le_zero
        exact Nat.sInf_le ⟨[], rfl, by simp [wprod]⟩
      omega
    refine ⟨∑ g ∈ y.coeff.support,
        Polynomial.C ((Matrix.trace (y.coeff g)).re / D) * (f g - X * gq) +
          Polynomial.C (h.eval 0) * (X * gq), ?_, ?_⟩
    · have hXg : (X * gq : ℝ[X]).natDegree ≤ (4 * (r + s + 3) * A + 1) * q := by
        refine natDegree_mul_le.trans ?_
        rw [natDegree_X]
        have : 1 + gq.natDegree ≤ (r + s + 2) * (q * (L + 1)) := by nlinarith
        exact this.trans hbig
      refine (natDegree_add_le_of_degree_le ?_ ?_)
      · refine natDegree_sum_le_of_forall_le _ _ fun g hg => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        simpa using natDegree_sub_le_of_le (((hfg g (hlen g hg)).1).trans hbig) hXg
      · exact (natDegree_C_mul_le _ _).trans hXg
    · intro n hn
      have hs := stp_pos s
      have hq'n : q * (L + 1) ≤ n := hq'C.trans hn
      have hn1 : 1 ≤ n := hq'.trans hq'n
      have hN : 1 ≤ stp s * n :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have hq'N : q * (L + 1) ≤ stp s * n := hq'n.trans (Nat.le_mul_of_pos_left _ (by omega))
      rw [specE_poly hD z hz _ hN (adm s n) h, ← hy]
      have hcast : (((stp s : ℕ) : ℝ) * n) = ((stp s * n : ℕ) : ℝ) := by push_cast; rfl
      rw [hcast]
      set N := stp s * n with hNdef
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      -- the denominator does not vanish: use `g = 1`
      have hgq : gq.eval (1 / (N : ℝ)) ≠ 0 := by
        intro h0
        have h1 := (hfg 1 hlen1).2 N (adm s n) hq'N
        rw [hNdef, expFix_one, h0, div_zero, mul_zero] at h1
        rw [← hNdef] at h1
        exact hNpos.ne' h1
      have hD' : (D : ℝ) ≠ 0 := by positivity
      have hterm : ∀ g ∈ y.coeff.support,
          (Matrix.trace (y.coeff g)).re * (expFix r s N g - 1) / ((D : ℝ) * N) =
            ((Matrix.trace (y.coeff g)).re / D) *
              ((f g).eval (1 / (N : ℝ)) - 1 / (N : ℝ) * gq.eval (1 / (N : ℝ))) /
                gq.eval (1 / (N : ℝ)) := by
        intro g hg
        rw [(hfg g (hlen g hg)).2 N (adm s n) hq'N]
        generalize (f g).eval (1 / (N : ℝ)) = F at *
        generalize gq.eval (1 / (N : ℝ)) = Gv at *
        field_simp
      rw [Finset.sum_div, Finset.sum_congr rfl hterm]
      simp only [eval_add, eval_finsetSum, eval_mul, eval_C, eval_sub, eval_X]
      rw [add_div, Finset.sum_div]
      congr 1
      generalize gq.eval (1 / (N : ℝ)) = Gv at *
      field_simp

/-! ## The upper tail -/

theorem upper_tail {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
      ‖regOp z‖ + ε ≤ ‖perpOp ω z‖)) atTop (𝓝 0) := by
  have hbnd : 0 ≤ bnd z := by
    unfold bnd
    exact Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => norm_nonneg _
  obtain ⟨C, hC⟩ := abstract_tail (bnd z + 1) (by linarith) (stp s) (stp_pos s)
    (fun n f => specE D r s (stp s * n) z f)
    (fun n f g => specE_add z hz _ f g)
    (fun n a f => specE_smul z hz _ a f)
    (fun n f g hfg => specE_mono z hz _ f g fun x hx =>
      hfg x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (fun n => specE_one_le z hz _)
    (hrat hD z hz)
    ‖regOp z‖ (norm_nonneg _) (aa z) (bb z)
    (ha hD z hz) (hb hD z hz)
    (fun δ hδ => ⟨1, fun p => by
      rw [one_mul]
      exact (abs_aa_le hD z p).trans (pow_le_pow_left₀ (norm_nonneg _) (by linarith) p)⟩)
    (hbgrow hD z)
    ε hε
  have hs := stp_pos s
  have hlim : Tendsto (fun n : ℕ => ((D : ℝ) * stp s * C) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => ?_) ?_
  · unfold PunctSketch.coinProb
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hN : 1 ≤ stp s * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    refine (tail_le hD z hz (stp s * n) hN (‖regOp z‖ + ε)).trans ?_
    have h1 := hC n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hDN : (0 : ℝ) ≤ (D : ℝ) * ((stp s * n : ℕ) : ℝ) := by positivity
    refine (mul_le_mul_of_nonneg_left h1 hDN).trans (le_of_eq ?_)
    push_cast
    field_simp

end BordenaveCollins.PartU

end
end

section
/-!
# The statements proved in Part U, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem upper_tail {D : ℕ} (hD : 1 ≤ D) (z : MG D r s) (hz : adj z = z) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
      ‖regOp z‖ + ε ≤ ‖perpOp ω z‖)) atTop (𝓝 0) :=
  PartU.upper_tail hD z hz ε hε

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

/-- `δ_g`. -/
def delta (g : Γ) : DerandSq.L2 Γ := lp.single 2 g (1 : ℂ)

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

/-! ### The vector state -/

/-- `e_a ⊗ δ_e`. -/
abbrev vv (D r s : ℕ) (a : Fin D) : EE D r s := PiLp.single 2 a (delta 1)

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

lemma re_tauOp_nonneg (X : (EE D r s) →L[ℂ] (EE D r s)) (hX : 0 ≤ X) : 0 ≤ (tauOp X).re := by
  have hpos : X.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive X).mp hX
  rw [tauOp_re]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hpos.re_inner_nonneg_right _)

/-! ### The faithfulness argument -/

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

/-- The moments are nonnegative. -/
theorem re_trTau_nonneg (x : MG D r s) (p : ℕ) : 0 ≤ (trTau ((adj x * x) ^ p)).re := by
  rw [trTau_eq_tauOp, regOp_adj_mul_pow]
  exact re_tauOp_nonneg _ (CStarAlgebra.pow_nonneg (star_mul_self_nonneg _) p)

/-- Faithfulness of the trace: moments of `x*x` recover the norm. -/
theorem faithful {D : ℕ} (hD : 1 ≤ D) (x : MG D r s) :
    Tendsto (fun p : ℕ => ((trTau ((adj x * x) ^ p)).re) ^ (1 / (2 * (p : ℝ)))) atTop
      (𝓝 ‖regOp x‖) := by
  exact BordenaveCollins.tendsto_re_trTau_pow_rpow hD x

end BordenaveCollins.PartL

end
end

section
/-!
# Part L: faithfulness of the trace and the lower tail

`faithful` is proved in `PartL_Faith.lean`. Here: `lower_tail`, from the trace formula
`trace_perpOp`, the positivity of `(Y* Y)^p`, Markov's inequality for the fixed-point counts and
`faithful`.
-/

open Finset Filter Topology
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartL

variable {r s : ℕ}

/-! ### Probabilities -/

lemma coinProb_nonneg {Ω : Type*} [Fintype Ω] (A : Ω → Prop) : 0 ≤ PunctSketch.coinProb A := by
  unfold PunctSketch.coinProb
  positivity

lemma coinProb_mono {Ω : Type*} [Fintype Ω] (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) :
    PunctSketch.coinProb A ≤ PunctSketch.coinProb B := by
  unfold PunctSketch.coinProb
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : (Finset.univ.filter A).card ≤ (Finset.univ.filter B).card :=
    Finset.card_le_card (by
      intro ω hω
      rw [Finset.mem_filter] at hω ⊢
      exact ⟨hω.1, h ω hω.2⟩)
  exact_mod_cast this

lemma coinProb_union {Ω ι : Type*} [Fintype Ω] (S : Finset ι) (A : ι → Ω → Prop) :
    PunctSketch.coinProb (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, PunctSketch.coinProb (A i) := by
  unfold PunctSketch.coinProb
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h : (Finset.univ.filter fun ω => ∃ i ∈ S, A i ω) ⊆
      S.biUnion fun i => Finset.univ.filter (A i) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hω ⊢
    exact hω
  have h2 := (Finset.card_le_card h).trans Finset.card_biUnion_le
  have h3 := (Nat.cast_le (α := ℝ)).mpr h2
  push_cast at h3
  convert h3
  rfl

/-- Markov's inequality for the number of fixed points. -/
lemma markov {N : ℕ} (g : G r s) (t : ℝ) (ht : 0 < t) :
    PunctSketch.coinProb (fun ω : Om r s N => t < (fixCount (act ω g) : ℝ)) ≤
      expFix r s N g / t := by
  unfold PunctSketch.coinProb expFix
  rw [div_right_comm]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [Finset.sum_div]
  have hcard : ((Finset.univ.filter fun ω : Om r s N => t < (fixCount (act ω g) : ℝ)).card : ℝ) =
      ∑ ω : Om r s N, if t < (fixCount (act ω g) : ℝ) then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  rw [hcard]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · exact (one_le_div ht).mpr h.le
  · positivity

/-! ### The deterministic inequality -/

lemma trR_pow_le_gen {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (Y : V →L[ℂ] V) (p : ℕ) (hp : 1 ≤ p) :
    PartO2.trR ((star Y * Y) ^ p) ≤ (Module.finrank ℂ V : ℝ) * ‖Y‖ ^ (2 * p) := by
  set T := star Y * Y with hTdef
  have hT : 0 ≤ T := star_mul_self_nonneg Y
  have hsa : IsSelfAdjoint (T ^ p) := (hT.isSelfAdjoint).pow p
  have h1 : T ^ p ≤ algebraMap ℝ _ ‖T ^ p‖ := hsa.le_algebraMap_norm_self
  have h2 := PartO2.trR_nonneg _ (sub_nonneg.mpr h1)
  rw [PartO2.trR_sub] at h2
  have h3 : PartO2.trR (algebraMap ℝ (V →L[ℂ] V) ‖T ^ p‖) =
      ‖T ^ p‖ * (Module.finrank ℂ V : ℝ) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, PartO2.trR_smul, PartO2.trR,
      PartO2.trL_one]
    simp
  have hTn : ‖T‖ = ‖Y‖ * ‖Y‖ := CStarRing.norm_star_mul_self
  have h4 : ‖T ^ p‖ ≤ ‖Y‖ ^ (2 * p) := by
    calc ‖T ^ p‖ ≤ ‖T‖ ^ p := norm_pow_le' T (by omega)
      _ = ‖Y‖ ^ (2 * p) := by rw [hTn, pow_mul, sq]
  have h5 : ‖T ^ p‖ * (Module.finrank ℂ V : ℝ) ≤ ‖Y‖ ^ (2 * p) * (Module.finrank ℂ V : ℝ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  linarith

lemma trR_pow_le {D N : ℕ}
    (Y : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
      PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) (p : ℕ) (hp : 1 ≤ p) :
    PartO2.trR ((star Y * Y) ^ p) ≤ (D : ℝ) * N * ‖Y‖ ^ (2 * p) := by
  have h := trR_pow_le_gen Y p hp
  rw [PartO2.finrank_space] at h
  push_cast at h
  exact h

lemma key_ineq {D N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (x : MG D r s) (p : ℕ) (hp : 1 ≤ p) :
    ∑ g ∈ ((adj x * x) ^ p).coeff.support,
        (Matrix.trace (((adj x * x) ^ p).coeff g)).re * ((fixCount (act ω g) : ℝ) - 1) ≤
      (D : ℝ) * N * ‖perpOp ω x‖ ^ (2 * p) := by
  rw [← PartO2.Lf_re]
  have h := PartO2.trL_pow hN ω (adj x * x) p
  rw [if_neg (by omega), add_zero] at h
  rw [← h, perpOp_mul hN, ← star_perpOp]
  exact trR_pow_le _ p hp

lemma det_bound {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (ω : Om r s N) (x : MG D r s) (p : ℕ)
    (hp : 1 ≤ p) (b η : ℝ) (hη : 0 ≤ η) (hY : ‖perpOp ω x‖ ^ (2 * p) ≤ b)
    (hgood : ∀ g ∈ ((adj x * x) ^ p).coeff.support.erase 1,
      (fixCount (act ω g) : ℝ) ≤ η * N) :
    (D : ℝ) * N * ((trTau ((adj x * x) ^ p)).re - b) ≤
      D * (trTau ((adj x * x) ^ p)).re +
        (∑ g ∈ ((adj x * x) ^ p).coeff.support.erase 1,
          |(Matrix.trace (((adj x * x) ^ p).coeff g)).re|) * (η * N + 1) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := key_ineq hN ω x p hp
  have h1' : (D : ℝ) * N * ‖perpOp ω x‖ ^ (2 * p) ≤ D * N * b :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have ha := PartU.aa_eq (adj x * x) p
  unfold PartU.aa at ha
  generalize (trTau ((adj x * x) ^ p)).re = a at ha ⊢
  generalize (adj x * x) ^ p = z at *
  set c : G r s → ℝ := fun g => (Matrix.trace (z.coeff g)).re with hc
  have h3 : c 1 = D * a := by
    rw [ha]; simp only [hc]; field_simp
  have hfix1 : (fixCount (act ω (1 : G r s)) : ℝ) = N := by simp [fixCount]
  have h2 : ∑ g ∈ z.coeff.support, c g * ((fixCount (act ω g) : ℝ) - 1) =
      c 1 * ((N : ℝ) - 1) + ∑ g ∈ z.coeff.support.erase 1,
        c g * ((fixCount (act ω g) : ℝ) - 1) := by
    by_cases h : (1 : G r s) ∈ z.coeff.support
    · rw [← Finset.add_sum_erase _ _ h, hfix1]
    · have h0 : c 1 = 0 := by
        simp only [hc]
        rw [Finsupp.notMem_support_iff.mp h]
        simp
      rw [Finset.erase_eq_of_notMem h, h0, zero_mul, zero_add]
  have h4 : -((∑ g ∈ z.coeff.support.erase 1, |c g|) * (η * N + 1)) ≤
      ∑ g ∈ z.coeff.support.erase 1, c g * ((fixCount (act ω g) : ℝ) - 1) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun g hg => ?_
    have hf := hgood g hg
    have hf0 : (0 : ℝ) ≤ (fixCount (act ω g) : ℝ) := by positivity
    have habs : |(fixCount (act ω g) : ℝ) - 1| ≤ η * N + 1 := by
      rw [abs_le]
      constructor
      · have : 0 ≤ η * N := by positivity
        linarith
      · linarith
    have := mul_le_mul_of_nonneg_left habs (abs_nonneg (c g))
    rw [← abs_mul] at this
    linarith [neg_abs_le (c g * ((fixCount (act ω g) : ℝ) - 1))]
  have h5 : (D : ℝ) * N * (a - b) = D * a * ((N : ℝ) - 1) - D * N * b + D * a := by ring
  rw [h3] at h2
  rw [h5]
  linarith

/-! ### The lower tail -/

theorem tendsto_N (s : ℕ) : Tendsto (fun n : ℕ => ((stp s * n : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have := PartU.stp_pos s
  exact_mod_cast Nat.le_mul_of_pos_left n (by omega)

theorem lower_tail {D : ℕ} (hD : 1 ≤ D) (x : MG D r s) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
      ‖perpOp ω x‖ ≤ ‖regOp x‖ - ε)) atTop (𝓝 0) := by
  set ρ := ‖regOp x‖ with hρ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hneg : ρ - ε < 0
  · have : (fun n : ℕ => PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
        ‖perpOp ω x‖ ≤ ρ - ε)) = fun _ => 0 := by
      funext n
      have h : ∀ ω : Om r s (stp s * n), ¬ (‖perpOp ω x‖ ≤ ρ - ε) := fun ω hω =>
        absurd (norm_nonneg (perpOp ω x)) (by linarith)
      simp [PunctSketch.coinProb, h]
    rw [this]
    exact tendsto_const_nhds
  push_neg at hneg
  -- choose `p`
  have hfa := faithful hD x
  obtain ⟨p, hp, hp1⟩ :=
    ((hfa.eventually (lt_mem_nhds (show ρ - ε < ρ by linarith))).and
      (eventually_ge_atTop 1)).exists
  set a := (trTau ((adj x * x) ^ p)).re with ha
  have ha0 : 0 ≤ a := re_trTau_nonneg x p
  set b := (ρ - ε) ^ (2 * p) with hb
  have hab : b < a := by
    by_contra hcon
    push_neg at hcon
    have h2 : (1 / (2 * (p : ℝ))) = ((2 * p : ℕ) : ℝ)⁻¹ := by push_cast; ring
    have : a ^ (1 / (2 * (p : ℝ))) ≤ ρ - ε := by
      calc a ^ (1 / (2 * (p : ℝ))) ≤ b ^ (1 / (2 * (p : ℝ))) :=
            Real.rpow_le_rpow ha0 hcon (by positivity)
        _ = ρ - ε := by rw [hb, h2, Real.pow_rpow_inv_natCast hneg (by omega)]
    linarith
  set S := ((adj x * x) ^ p).coeff.support.erase 1 with hS
  set C := ∑ g ∈ S, |(Matrix.trace (((adj x * x) ^ p).coeff g)).re| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun g _ => abs_nonneg _
  set gap := a - b with hgap
  have hgap0 : 0 < gap := by linarith
  set η := gap * D / (2 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- the dominating sequence
  have hlim : Tendsto (fun n : ℕ => ∑ g ∈ S,
      expFix r s (stp s * n) g / (η * ((stp s * n : ℕ) : ℝ))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ∑ g ∈ S,
        expFix r s (stp s * n) g / (η * ((stp s * n : ℕ) : ℝ))) atTop
        (𝓝 (∑ _g ∈ S, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun g hg => ?_
      have hg1 : g ≠ 1 := (Finset.mem_erase.mp hg).1
      exact (tendsto_expFix g hg1).div_atTop ((tendsto_N s).const_mul_atTop hη0)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => coinProb_nonneg _) ?_
  set K := (D * a + C) / (D * gap / 2) with hK
  filter_upwards [eventually_ge_atTop 1, (tendsto_N s).eventually (eventually_gt_atTop K)]
    with n hn hKn
  have hs := PartU.stp_pos s
  have hN : 1 ≤ stp s * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hN' : (0 : ℝ) < ((stp s * n : ℕ) : ℝ) := by exact_mod_cast hN
  have hsub : ∀ ω : Om r s (stp s * n), ‖perpOp ω x‖ ≤ ρ - ε →
      ∃ g ∈ S, η * ((stp s * n : ℕ) : ℝ) < (fixCount (act ω g) : ℝ) := by
    intro ω hω
    by_contra hcon
    push_neg at hcon
    have hY : ‖perpOp ω x‖ ^ (2 * p) ≤ b := pow_le_pow_left₀ (norm_nonneg _) hω _
    have h := det_bound hD hN ω x p hp1 b η hη0.le hY hcon
    rw [← ha, ← hC, ← hgap] at h
    have hCη : C * (η * ((stp s * n : ℕ) : ℝ)) ≤ D * ((stp s * n : ℕ) : ℝ) * gap / 2 := by
      have e : C * (η * ((stp s * n : ℕ) : ℝ)) =
          (C / (C + 1)) * (D * ((stp s * n : ℕ) : ℝ) * gap / 2) := by
        rw [hη]; field_simp
      rw [e]
      have h1 : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      exact mul_le_of_le_one_left (by positivity) h1
    have hK2 : D * a + C < D * gap / 2 * ((stp s * n : ℕ) : ℝ) := by
      rw [hK, div_lt_iff₀ (by positivity)] at hKn
      linarith
    nlinarith
  calc PunctSketch.coinProb (fun ω : Om r s (stp s * n) => ‖perpOp ω x‖ ≤ ρ - ε)
      ≤ PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
          ∃ g ∈ S, η * ((stp s * n : ℕ) : ℝ) < (fixCount (act ω g) : ℝ)) :=
        coinProb_mono _ _ hsub
    _ ≤ ∑ g ∈ S, PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
          η * ((stp s * n : ℕ) : ℝ) < (fixCount (act ω g) : ℝ)) := coinProb_union S _
    _ ≤ ∑ g ∈ S, expFix r s (stp s * n) g / (η * ((stp s * n : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun g _ => markov g _ (by positivity)

end BordenaveCollins.PartL

end
end

section
/-!
# The statements proved in Part L, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem lower_tail {D : ℕ} (hD : 1 ≤ D) (x : MG D r s) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
      ‖perpOp ω x‖ ≤ ‖regOp x‖ - ε)) atTop (𝓝 0) :=
  PartL.lower_tail hD x ε hε

end BordenaveCollins

end
end

section
/-!
# Part T: the core theorem (`core`)

From `upper_tail` (applied to `z = adj x * x`) and `lower_tail`.
-/

open Finset Filter Topology
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartT

open BordenaveCollins

variable {r s : ℕ}

/-! ## The adjoint on `MG D r s` -/

section Adj
variable {D : ℕ}

theorem adj_eq_sum (x : MG D r s) :
    adj x = x.coeff.sum fun g A => MonoidAlgebra.single g⁻¹ A.conjTranspose := rfl

theorem adj_zero : adj (0 : MG D r s) = 0 := by
  simp [adj]

theorem adj_add (x y : MG D r s) : adj (x + y) = adj x + adj y := by
  rw [adj_eq_sum, adj_eq_sum, adj_eq_sum, MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun g => by simp)
    (fun g A B => by rw [Matrix.conjTranspose_add, MonoidAlgebra.single_add])

theorem adj_single (g : G r s) (A : Matrix (Fin D) (Fin D) ℂ) :
    adj (MonoidAlgebra.single g A) = MonoidAlgebra.single g⁻¹ A.conjTranspose := by
  rw [adj_eq_sum, MonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)

theorem adj_mul (x y : MG D r s) : adj (x * y) = adj y * adj x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, adj_zero, mul_zero]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, adj_add, adj_add, h₁, h₂, mul_add]
  | single g A =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, adj_zero, zero_mul]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, adj_add, adj_add, h₁, h₂, add_mul]
    | single h B =>
      rw [MonoidAlgebra.single_mul_single, adj_single, adj_single, adj_single,
        MonoidAlgebra.single_mul_single, Matrix.conjTranspose_mul, PartF1.g_mul_inv_rev]

theorem adj_adj (x : MG D r s) : adj (adj x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [adj_zero, adj_zero]
  | add x₁ x₂ h₁ h₂ => rw [adj_add, adj_add, h₁, h₂]
  | single g A =>
    rw [adj_single, adj_single, Matrix.conjTranspose_conjTranspose, PartF1.g_inv_inv]

theorem adj_adj_mul_self (x : MG D r s) : adj (adj x * x) = adj x * x := by
  rw [adj_mul, adj_adj]

end Adj

/-! ## The left-regular representation -/

theorem star_leftReg_gen {Γ : Type*} [Group Γ] (g : Γ) :
    star (DerandSq.leftReg g : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = DerandSq.leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [PartO1.leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

theorem star_leftReg (g : G r s) :
    star (DerandSq.leftReg g : DerandSq.L2 (G r s) →L[ℂ] DerandSq.L2 (G r s)) =
      DerandSq.leftReg g⁻¹ :=
  star_leftReg_gen g

/-- The left-regular representation of `G r s` as a monoid homomorphism. -/
def lregHom (r s : ℕ) :
    G r s →* (DerandSq.L2 (G r s) →L[ℂ] DerandSq.L2 (G r s)) where
  toFun g := DerandSq.leftReg g
  map_one' := PartO1.leftReg_one
  map_mul' a b := PartO1.leftReg_mul a b

section Norms
variable {D : ℕ}

theorem regOp_mul (x y : MG D r s) : regOp (x * y) = regOp x * regOp y :=
  opOf_mul (lregHom r s) x y

theorem regOp_adj (x : MG D r s) : regOp (adj x) = star (regOp x) :=
  (opOf_adj (fun g : G r s => DerandSq.leftReg g) star_leftReg x).symm

theorem norm_star_mul_self_gen {A : Type*} [CStarAlgebra A] (y : A) :
    ‖star y * y‖ = ‖y‖ * ‖y‖ := CStarRing.norm_star_mul_self

theorem norm_regOp_sq (x : MG D r s) : ‖regOp (adj x * x)‖ = ‖regOp x‖ * ‖regOp x‖ := by
  have h := norm_star_mul_self_gen (regOp x)
  rw [regOp_mul, regOp_adj]
  exact h

theorem norm_perpOp_sq {N : ℕ} (hN : 1 ≤ N) (ω : Om r s N) (x : MG D r s) :
    ‖perpOp ω (adj x * x)‖ = ‖perpOp ω x‖ * ‖perpOp ω x‖ := by
  have h := norm_star_mul_self_gen (perpOp ω x)
  rw [perpOp_mul hN, ← star_perpOp]
  exact h

end Norms

/-! ## Uniform probability -/

theorem coinProb_nonneg {Ω : Type*} [Fintype Ω] (A : Ω → Prop) :
    0 ≤ PunctSketch.coinProb A := by
  unfold PunctSketch.coinProb
  positivity

theorem coinProb_le_add {Ω : Type*} [Fintype Ω] (A B C : Ω → Prop)
    (h : ∀ ω, A ω → B ω ∨ C ω) :
    PunctSketch.coinProb A ≤ PunctSketch.coinProb B + PunctSketch.coinProb C := by
  unfold PunctSketch.coinProb
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have h1 : (univ.filter A) ⊆ (univ.filter B) ∪ (univ.filter C) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and, mem_union] at hω ⊢
    exact h ω hω
  have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  exact_mod_cast h2

/-! ## The core theorem -/

theorem core {D : ℕ} (x : MG D r s) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
      ε ≤ |‖perpOp ω x‖ - ‖regOp x‖|)) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    have h1 : ‖regOp x‖ = 0 := by
      have : regOp x = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
      rw [this, norm_zero]
    have h2 : ∀ (N : ℕ) (ω : Om r s N), ‖perpOp ω x‖ = 0 := by
      intro N ω
      have : perpOp ω x = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
      rw [this, norm_zero]
    have h3 : ∀ n : ℕ, PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
        ε ≤ |‖perpOp ω x‖ - ‖regOp x‖|) = 0 := by
      intro n
      unfold PunctSketch.coinProb
      have : (univ.filter fun ω : Om r s (stp s * n) =>
          ε ≤ |‖perpOp ω x‖ - ‖regOp x‖|) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun ω _ => ?_
        rw [h1, h2, sub_zero, abs_zero]
        exact not_le.mpr hε
      rw [this]
      simp
    simp only [h3]
    exact tendsto_const_nhds
  · have hz : adj (adj x * x) = adj x * x := adj_adj_mul_self x
    have hup := upper_tail hD (adj x * x) hz (ε ^ 2) (by positivity)
    have hlo := lower_tail hD x ε hε
    have hsum := hup.add hlo
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => coinProb_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs := PartU.stp_pos s
    have hN : 1 ≤ stp s * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    refine coinProb_le_add _ _ _ fun ω hω => ?_
    rw [norm_regOp_sq, norm_perpOp_sq hN]
    have ha : 0 ≤ ‖regOp x‖ := norm_nonneg _
    by_cases hc : ‖perpOp ω x‖ ≤ ‖regOp x‖ - ε
    · exact Or.inr hc
    · left
      rw [not_le] at hc
      have h4 : ‖regOp x‖ + ε ≤ ‖perpOp ω x‖ := by
        rcases le_abs.mp hω with h | h
        · linarith
        · linarith
      nlinarith

end BordenaveCollins.PartT

end
end

section
/-!
# The statements proved in Part T, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem core {D : ℕ} (x : MG D r s) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => PunctSketch.coinProb (fun ω : Om r s (stp s * n) =>
      ε ≤ |‖perpOp ω x‖ - ‖regOp x‖|)) atTop (𝓝 0) :=
  PartT.core x ε hε

end BordenaveCollins

end
end

section
/-!
# Part B: the bridge to `DerandSq.theorem_2_14`

`eval_model`, `eval_reg` (a polynomial evaluated at the model / at the left-regular
representation is `opOf` of its image in the group algebra), `part_two` (from `core`) and
`part_one` (transport along `FreeGroup (Fin r) ≃* G r 0`).
-/

open Finset Filter Topology
open scoped Classical

noncomputable section

namespace BordenaveCollins.PartB

open BordenaveCollins AccessibleMaps

variable {r s : ℕ}

/-! ## Words in a monoid -/

section Gen
variable {D : ℕ} {ι : Type*}

/-- The product of the letters of a word, for a letter map into a monoid. -/
def wordGen {M : Type*} [Monoid M] (lg : ι ⊕ ι → M) (w : FreeMonoid (ι ⊕ ι)) : M :=
  (w.toList.map lg).prod

theorem wordOp_eq {M : Type*} [Monoid M] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (π : M →* (E →L[ℂ] E)) (u : ι → E →L[ℂ] E)
    (lg : ι ⊕ ι → M) (h : ∀ l, DerandSq.letterOp u l = π (lg l)) (w : FreeMonoid (ι ⊕ ι)) :
    DerandSq.wordOp u w = π (wordGen lg w) := by
  unfold DerandSq.wordOp wordGen
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => h l

/-- A polynomial in the group algebra, for a letter map into `G r s`. -/
def toAlgGen (lg : ι ⊕ ι → G r s) (P : DerandSq.NCPoly D ι) : MG D r s :=
  P.sum fun w A => MonoidAlgebra.single (wordGen lg w) A

theorem opOf_toAlgGen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G r s → H →L[ℂ] H) (lg : ι ⊕ ι → G r s) (P : DerandSq.NCPoly D ι) :
    opOf π (toAlgGen lg P) = ∑ w ∈ P.support, tensorOp (P w) (π (wordGen lg w)) := by
  rw [← PartO1.opHom_apply, toAlgGen, map_finsuppSum]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun w _ => ?_
  exact PartO1.opOf_single π (wordGen lg w) (P w)

theorem eval_eq_opOf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (π : G r s →* (E →L[ℂ] E)) (u : ι → E →L[ℂ] E)
    (lg : ι ⊕ ι → G r s) (h : ∀ l, DerandSq.letterOp u l = π (lg l))
    (P : DerandSq.NCPoly D ι) :
    P.eval u = opOf (fun g => π g) (toAlgGen lg P) := by
  rw [opOf_toAlgGen]
  unfold DerandSq.NCPoly.eval
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [wordOp_eq π u lg h]

end Gen

/-! ## The left-regular representation -/

theorem star_leftReg_gen {Γ : Type*} [Group Γ] (g : Γ) :
    star (DerandSq.leftReg g : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = DerandSq.leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [PartO1.leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

/-- The left-regular representation of `G r s` as a monoid homomorphism. -/
def lregHom (r s : ℕ) :
    G r s →* (DerandSq.L2 (G r s) →L[ℂ] DerandSq.L2 (G r s)) where
  toFun g := DerandSq.leftReg g
  map_one' := PartO1.leftReg_one
  map_mul' a b := PartO1.leftReg_mul a b

/-! ## `eval_model` and `eval_reg` -/

theorem pm_inv {N : ℕ} (σ : DerandSq.PM N) : (σ.1)⁻¹ = σ.1 := by
  refine Equiv.ext fun x => ?_
  exact Equiv.Perm.inv_eq_iff_eq.mpr (σ.2 x).1.symm

theorem inr_mGen_inv (j : Fin s) :
    (Monoid.Coprod.inr (DerandSq.mGen j) : G r s)⁻¹ = Monoid.Coprod.inr (DerandSq.mGen j) := by
  apply PartF1.g_inv_eq_of_mul_eq_one_right
  rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem eval_model {D N : ℕ} (P : DerandSq.NCPoly D (Fin r ⊕ Fin s)) (ω : Om r s N) :
    P.eval (Sum.elim (fun i => DerandSq.permOp (ω.1 i)) (fun j => DerandSq.permOp (ω.2 j).1)) =
      modelOp ω (toAlg P) := by
  refine eval_eq_opOf (PartO1.permHom ω) _ letterG (fun l => ?_) P
  rw [PartO1.permHom_apply]
  rcases l with (i | j) | (i | j)
  · show DerandSq.permOp (ω.1 i) = _
    rw [show letterG (Sum.inl (Sum.inl i)) = genL (r := r) (s := s) (Sum.inl (i, true)) from rfl,
      PartF1.act_genL]
    rfl
  · show DerandSq.permOp (ω.2 j).1 = _
    rw [show letterG (Sum.inl (Sum.inr j)) = genL (r := r) (s := s) (Sum.inr j) from rfl,
      PartF1.act_genL]
    rfl
  · show star (DerandSq.permOp (ω.1 i)) = _
    rw [show letterG (Sum.inr (Sum.inl i)) = genL (r := r) (s := s) (Sum.inl (i, false)) from rfl,
      PartF1.act_genL, PartO1.star_permOp]
    rfl
  · show star (DerandSq.permOp (ω.2 j).1) = _
    rw [show letterG (Sum.inr (Sum.inr j)) = genL (r := r) (s := s) (Sum.inr j) from rfl,
      PartF1.act_genL, PartO1.star_permOp, pm_inv]
    rfl

theorem eval_reg {D : ℕ} (P : DerandSq.NCPoly D (Fin r ⊕ Fin s)) :
    P.eval (Sum.elim
        (fun i => DerandSq.leftReg (Monoid.Coprod.inl (FreeGroup.of i) : G r s))
        (fun j => DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) : G r s))) =
      regOp (toAlg P) := by
  refine eval_eq_opOf (lregHom r s) _ letterG (fun l => ?_) P
  show _ = DerandSq.leftReg (letterG l)
  rcases l with (i | j) | (i | j)
  · rfl
  · rfl
  · show star (DerandSq.leftReg (Monoid.Coprod.inl (FreeGroup.of i) : G r s)) = _
    exact star_leftReg_gen _
  · show star (DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) : G r s)) =
      DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) : G r s)
    have h := star_leftReg_gen (Monoid.Coprod.inr (DerandSq.mGen j) : G r s)
    rw [inr_mGen_inv] at h
    exact h

/-! ## `part_two` -/

theorem tendsto_two_mul : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩

theorem part_two (D r s : ℕ) (ε : ℝ) (hε : 0 < ε) (P : DerandSq.NCPoly D (Fin r ⊕ Fin s)) :
    Filter.Tendsto (fun n : ℕ =>
        PunctSketch.coinProb (fun UM : (Fin r → Equiv.Perm (Fin (2 * n))) ×
            (Fin s → DerandSq.PM (2 * n)) =>
          ε ≤ |‖DerandSq.perpCompress D (2 * n)
                (P.eval (Sum.elim (fun i => DerandSq.permOp (UM.1 i))
                  (fun j => DerandSq.permOp (UM.2 j).1)))‖ -
            ‖P.eval (Sum.elim
                (fun i => DerandSq.leftReg (Monoid.Coprod.inl (FreeGroup.of i) :
                  Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s)))
                (fun j => DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) :
                  Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s))))‖|))
      Filter.atTop (nhds 0) := by
  have key : ∀ (N : ℕ) (UM : (Fin r → Equiv.Perm (Fin N)) × (Fin s → DerandSq.PM N)),
      (ε ≤ |‖DerandSq.perpCompress D N
                (P.eval (Sum.elim (fun i => DerandSq.permOp (UM.1 i))
                  (fun j => DerandSq.permOp (UM.2 j).1)))‖ -
            ‖P.eval (Sum.elim
                (fun i => DerandSq.leftReg (Monoid.Coprod.inl (FreeGroup.of i) :
                  Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s)))
                (fun j => DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) :
                  Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s))))‖|) =
        (ε ≤ |‖perpOp (r := r) (s := s) UM (toAlg P)‖ - ‖regOp (toAlg P)‖|) := by
    intro N UM
    rw [eval_reg, eval_model P UM, perpOp]
  simp only [key]
  let F : ℕ → ℝ := fun N => PunctSketch.coinProb (fun ω : Om r s N =>
    ε ≤ |‖perpOp ω (toAlg P)‖ - ‖regOp (toAlg P)‖|)
  have hF : Tendsto (fun n : ℕ => F (2 * n)) atTop (𝓝 0) := by
    have hcore : Tendsto (fun n : ℕ => F (stp s * n)) atTop (𝓝 0) := core (toAlg P) ε hε
    by_cases hs : s = 0
    · have h1 : stp s = 1 := by simp [stp, hs]
      simp only [h1, one_mul] at hcore
      exact hcore.comp tendsto_two_mul
    · have h2 : stp s = 2 := by simp [stp, hs]
      simpa only [h2] using hcore
  exact hF

/-! ## Transport along a group isomorphism -/

section Transport

/-- Reindexing `ℓ²` along a bijection. -/
def reidx {α β : Type*} (e : α ≃ β) : DerandSq.L2 α ≃ₗᵢ[ℂ] DerandSq.L2 β where
  toFun f := ⟨fun h => f (e.symm h), by
    have hf := lp.memℓp f
    rw [memℓp_gen_iff (by norm_num)] at hf
    show Memℓp (fun h : β => f (e.symm h)) 2
    rw [memℓp_gen_iff (by norm_num)]
    exact e.symm.summable_iff.mpr hf⟩
  map_add' f f' := by ext h; rfl
  map_smul' c f := by ext h; rfl
  invFun f := ⟨fun h => f (e h), by
    have hf := lp.memℓp f
    rw [memℓp_gen_iff (by norm_num)] at hf
    show Memℓp (fun h : α => f (e h)) 2
    rw [memℓp_gen_iff (by norm_num)]
    exact e.summable_iff.mpr hf⟩
  left_inv f := by
    ext h
    show f (e.symm (e h)) = f h
    rw [e.symm_apply_apply]
  right_inv f := by
    ext h
    show f (e (e.symm h)) = f h
    rw [e.apply_symm_apply]
  norm_map' f := by
    show ‖(⟨fun h => f (e.symm h), _⟩ : DerandSq.L2 β)‖ = ‖f‖
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal)

theorem reidx_apply {α β : Type*} (e : α ≃ β) (f : DerandSq.L2 α) (h : β) :
    reidx e f h = f (e.symm h) := rfl

theorem reidx_leftReg {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ') (g : Γ)
    (f : DerandSq.L2 Γ) :
    reidx e.toEquiv (DerandSq.leftReg g f) = DerandSq.leftReg (e g) (reidx e.toEquiv f) := by
  ext h
  rw [reidx_apply, PartO1.leftReg_apply, PartO1.leftReg_apply, reidx_apply]
  refine congrArg _ ?_
  show g⁻¹ * e.symm h = e.symm ((e g)⁻¹ * h)
  rw [map_mul, map_inv, e.symm_apply_apply]

theorem norm_eq_of_intertwine {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (W : E ≃ₗᵢ[ℂ] E') (T : E →L[ℂ] E)
    (T' : E' →L[ℂ] E') (h : ∀ y, T' (W y) = W (T y)) : ‖T'‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    have h1 := h (W.symm y)
    rw [W.apply_symm_apply] at h1
    calc ‖T' y‖ = ‖T (W.symm y)‖ := by rw [h1, W.norm_map]
      _ ≤ ‖T‖ * ‖W.symm y‖ := T.le_opNorm _
      _ = ‖T‖ * ‖y‖ := by rw [W.symm.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    calc ‖T y‖ = ‖T' (W y)‖ := by rw [h, W.norm_map]
      _ ≤ ‖T'‖ * ‖W y‖ := T'.le_opNorm _
      _ = ‖T'‖ * ‖y‖ := by rw [W.norm_map]

theorem norm_sum_tensor_eq {D : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    {κ : Type*} (S : Finset κ) (A : κ → Matrix (Fin D) (Fin D) ℂ) (gs : κ → Γ) :
    ‖∑ w ∈ S, tensorOp (A w) (DerandSq.leftReg (e (gs w)))‖ =
      ‖∑ w ∈ S, tensorOp (A w) (DerandSq.leftReg (gs w))‖ := by
  refine norm_eq_of_intertwine
    (LinearIsometryEquiv.piLpCongrRight 2 fun _ : Fin D => reidx e.toEquiv) _ _ fun y => ?_
  ext a : 1
  simp only [_root_.sum_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PartO1.tensorOp_apply, map_sum, map_smul, reidx_leftReg]

end Transport

/-! ## `part_one` -/

theorem coinProb_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω') (A : Ω' → Prop) :
    PunctSketch.coinProb (fun ω => A (e ω)) = PunctSketch.coinProb A := by
  unfold PunctSketch.coinProb
  rw [Fintype.card_congr e]
  congr 2
  exact Finset.card_bij (fun a _ => e a) (by simp) (fun a _ b _ h => e.injective h)
    (fun b hb => ⟨e.symm b, by simpa using hb, by simp⟩)

theorem gam0_eq_one (y : DerandSq.Gam 0) : y = 1 := by
  induction y using Monoid.CoprodI.induction_on with
  | one => rfl
  | of i m => exact i.elim0
  | mul a b ha hb => rw [ha, hb, mul_one]

/-- `F_r ≃* F_r * Γ_0`. -/
def isoF (r : ℕ) : FreeGroup (Fin r) ≃* G r 0 where
  toFun := Monoid.Coprod.inl
  invFun := Monoid.Coprod.fst
  left_inv g := Monoid.Coprod.fst_apply_inl g
  right_inv g := by
    have h : ((Monoid.Coprod.inl : FreeGroup (Fin r) →* G r 0).comp Monoid.Coprod.fst) =
        MonoidHom.id _ := by
      apply Monoid.Coprod.hom_ext
      · refine MonoidHom.ext fun g => ?_
        simp
      · refine MonoidHom.ext fun y => ?_
        rw [gam0_eq_one y]
        simp
    exact DFunLike.congr_fun h g
  map_mul' := map_mul _

/-- The letters in the free group. -/
def lgF (r : ℕ) : Fin r ⊕ Fin r → FreeGroup (Fin r)
  | Sum.inl i => FreeGroup.of i
  | Sum.inr i => (FreeGroup.of i)⁻¹

/-- The letters in `G r 0`. -/
def lg0 (r : ℕ) (l : Fin r ⊕ Fin r) : G r 0 := Monoid.Coprod.inl (lgF r l)

theorem wordGen_lg0 (w : FreeMonoid (Fin r ⊕ Fin r)) :
    wordGen (lg0 r) w = isoF r (wordGen (lgF r) w) := by
  unfold wordGen
  rw [map_list_prod, List.map_map]
  rfl

/-- The sample space with no matchings. -/
def omEquiv (r N : ℕ) : Om r 0 N ≃ (Fin r → Equiv.Perm (Fin N)) where
  toFun ω := ω.1
  invFun U := (U, fun j => j.elim0)
  left_inv _ := Prod.ext rfl (funext fun j => j.elim0)
  right_inv _ := rfl

theorem eval_model0 {D N : ℕ} (P : DerandSq.NCPoly D (Fin r)) (ω : Om r 0 N) :
    P.eval (fun i => DerandSq.permOp (ω.1 i)) = modelOp ω (toAlgGen (lg0 r) P) := by
  refine eval_eq_opOf (PartO1.permHom ω) _ (lg0 r) (fun l => ?_) P
  rw [PartO1.permHom_apply]
  rcases l with i | i
  · show DerandSq.permOp (ω.1 i) = _
    congr 1
  · show star (DerandSq.permOp (ω.1 i)) = _
    rw [PartO1.star_permOp]
    congr 1

theorem norm_eval_reg0 {D : ℕ} (P : DerandSq.NCPoly D (Fin r)) :
    ‖P.eval (fun i => DerandSq.leftReg (FreeGroup.of i))‖ = ‖regOp (toAlgGen (lg0 r) P)‖ := by
  have h1 : P.eval (fun i => DerandSq.leftReg (FreeGroup.of i)) =
      ∑ w ∈ P.support, tensorOp (P w) (DerandSq.leftReg (wordGen (lgF r) w)) := by
    unfold DerandSq.NCPoly.eval
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [wordOp_eq (PartO1.regHom (FreeGroup (Fin r))) _ (lgF r) (fun l => ?_)]
    · rfl
    · rcases l with i | i
      · rfl
      · show star (DerandSq.leftReg (FreeGroup.of i)) = DerandSq.leftReg (FreeGroup.of i)⁻¹
        exact star_leftReg_gen _
  have h2 : regOp (toAlgGen (lg0 r) P) =
      ∑ w ∈ P.support, tensorOp (P w) (DerandSq.leftReg (isoF r (wordGen (lgF r) w))) := by
    unfold regOp
    rw [opOf_toAlgGen]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [wordGen_lg0]
  have h3 := norm_sum_tensor_eq (Γ' := G r 0) (isoF r) P.support (fun w => P w) (wordGen (lgF r))
  exact (congrArg norm h1).trans (h3.symm.trans (congrArg norm h2).symm)

theorem part_one (D r : ℕ) (ε : ℝ) (hε : 0 < ε) (P : DerandSq.NCPoly D (Fin r)) :
    Filter.Tendsto (fun N : ℕ => PunctSketch.coinProb (fun U : Fin r → Equiv.Perm (Fin N) =>
        ε ≤ |‖DerandSq.perpCompress D N (P.eval (fun i => DerandSq.permOp (U i)))‖ -
          ‖P.eval (fun i => DerandSq.leftReg (FreeGroup.of i))‖|))
      Filter.atTop (nhds 0) := by
  have key : ∀ (N : ℕ) (ω : Om r 0 N),
      (ε ≤ |‖DerandSq.perpCompress D N
            (P.eval (fun i => DerandSq.permOp (omEquiv r N ω i)))‖ -
          ‖P.eval (fun i => DerandSq.leftReg (FreeGroup.of i))‖|) =
        (ε ≤ |‖perpOp ω (toAlgGen (lg0 r) P)‖ - ‖regOp (toAlgGen (lg0 r) P)‖|) := by
    intro N ω
    rw [norm_eval_reg0, perpOp, ← eval_model0 P ω]
    rfl
  have key2 : ∀ N : ℕ, PunctSketch.coinProb (fun U : Fin r → Equiv.Perm (Fin N) =>
        ε ≤ |‖DerandSq.perpCompress D N (P.eval (fun i => DerandSq.permOp (U i)))‖ -
          ‖P.eval (fun i => DerandSq.leftReg (FreeGroup.of i))‖|) =
      PunctSketch.coinProb (fun ω : Om r 0 N =>
        ε ≤ |‖perpOp ω (toAlgGen (lg0 r) P)‖ - ‖regOp (toAlgGen (lg0 r) P)‖|) := by
    intro N
    rw [← coinProb_equiv (omEquiv r N)]
    simp only [key]
  simp only [key2]
  let F : ℕ → ℝ := fun N => PunctSketch.coinProb (fun ω : Om r 0 N =>
    ε ≤ |‖perpOp ω (toAlgGen (lg0 r) P)‖ - ‖regOp (toAlgGen (lg0 r) P)‖|)
  have hF : Tendsto F atTop (𝓝 0) := by
    have hcore : Tendsto (fun n : ℕ => F (stp 0 * n)) atTop (𝓝 0) :=
      core (toAlgGen (lg0 r) P) ε hε
    have h1 : stp 0 = 1 := by simp [stp]
    simpa only [h1, one_mul] using hcore
  exact hF

end BordenaveCollins.PartB

end
end

section
/-!
# The statements proved in Part B, under their Blueprint names
-/

open Finset Filter Topology Polynomial
open scoped Classical

noncomputable section

namespace BordenaveCollins

variable {r s : ℕ}

theorem part_two (D r s : ℕ) (ε : ℝ) (hε : 0 < ε) (P : DerandSq.NCPoly D (Fin r ⊕ Fin s)) :
    Filter.Tendsto (fun n : ℕ =>
        PunctSketch.coinProb (fun UM : (Fin r → Equiv.Perm (Fin (2 * n))) ×
            (Fin s → DerandSq.PM (2 * n)) =>
          ε ≤ |‖DerandSq.perpCompress D (2 * n)
                (P.eval (Sum.elim (fun i => DerandSq.permOp (UM.1 i))
                  (fun j => DerandSq.permOp (UM.2 j).1)))‖ -
            ‖P.eval (Sum.elim
                (fun i => DerandSq.leftReg (Monoid.Coprod.inl (FreeGroup.of i) :
                  Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s)))
                (fun j => DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) :
                  Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s))))‖|))
      Filter.atTop (nhds 0) :=
  PartB.part_two D r s ε hε P

theorem part_one (D r : ℕ) (ε : ℝ) (hε : 0 < ε) (P : DerandSq.NCPoly D (Fin r)) :
    Filter.Tendsto (fun N : ℕ => PunctSketch.coinProb (fun U : Fin r → Equiv.Perm (Fin N) =>
        ε ≤ |‖DerandSq.perpCompress D N (P.eval (fun i => DerandSq.permOp (U i)))‖ -
          ‖P.eval (fun i => DerandSq.leftReg (FreeGroup.of i))‖|))
      Filter.atTop (nhds 0) :=
  PartB.part_one D r ε hε P

end BordenaveCollins

end
end

section
/-!
# `DerandSq.theorem_2_14` (Bordenave–Collins), assembled
-/

noncomputable section

namespace BordenaveCollins

theorem theorem_2_14 (D r s : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∀ P : DerandSq.NCPoly D (Fin r),
      Filter.Tendsto (fun N : ℕ => PunctSketch.coinProb (fun U : Fin r → Equiv.Perm (Fin N) =>
          ε ≤ |‖DerandSq.perpCompress D N (P.eval (fun i => DerandSq.permOp (U i)))‖ -
            ‖P.eval (fun i => DerandSq.leftReg (FreeGroup.of i))‖|))
        Filter.atTop (nhds 0)) ∧
    (∀ P : DerandSq.NCPoly D (Fin r ⊕ Fin s),
      Filter.Tendsto (fun n : ℕ =>
          PunctSketch.coinProb (fun UM : (Fin r → Equiv.Perm (Fin (2 * n))) ×
              (Fin s → DerandSq.PM (2 * n)) =>
            ε ≤ |‖DerandSq.perpCompress D (2 * n)
                  (P.eval (Sum.elim (fun i => DerandSq.permOp (UM.1 i))
                    (fun j => DerandSq.permOp (UM.2 j).1)))‖ -
              ‖P.eval (Sum.elim
                  (fun i => DerandSq.leftReg (Monoid.Coprod.inl (FreeGroup.of i) :
                    Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s)))
                  (fun j => DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) :
                    Monoid.Coprod (FreeGroup (Fin r)) (DerandSq.Gam s))))‖|))
        Filter.atTop (nhds 0)) :=
  ⟨fun P => part_one D r ε hε P, fun P => part_two D r s ε hε P⟩

end BordenaveCollins

end
end

section
open DerandSq

theorem solution (D r s : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∀ P : NCPoly D (Fin r),
      Filter.Tendsto (fun N : ℕ => PunctSketch.coinProb (fun U : Fin r → Equiv.Perm (Fin N) =>
          ε ≤ |‖perpCompress D N (P.eval (fun i => permOp (U i)))‖ -
            ‖P.eval (fun i => leftReg (FreeGroup.of i))‖|))
        Filter.atTop (nhds 0)) ∧
    (∀ P : NCPoly D (Fin r ⊕ Fin s),
      Filter.Tendsto (fun n : ℕ =>
          PunctSketch.coinProb (fun UM : (Fin r → Equiv.Perm (Fin (2 * n))) × (Fin s → PM (2 * n)) =>
            ε ≤ |‖perpCompress D (2 * n)
                  (P.eval (Sum.elim (fun i => permOp (UM.1 i)) (fun j => permOp (UM.2 j).1)))‖ -
              ‖P.eval (Sum.elim
                  (fun i => leftReg (Monoid.Coprod.inl (FreeGroup.of i) :
                    Monoid.Coprod (FreeGroup (Fin r)) (Gam s)))
                  (fun j => leftReg (Monoid.Coprod.inr (mGen j) :
                    Monoid.Coprod (FreeGroup (Fin r)) (Gam s))))‖|))
        Filter.atTop (nhds 0)) :=
  BordenaveCollins.theorem_2_14 D r s ε hε

end
