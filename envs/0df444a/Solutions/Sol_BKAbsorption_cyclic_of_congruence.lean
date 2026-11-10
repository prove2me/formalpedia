-- Prove2me | solution 1 for BKAbsorption.cyclic_of_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T16:17:25.929256+00:00
-- url     : https://prove2.me/submissions/28b13ebd-c8bf-4f38-b6d6-d0fcccfa4aad

import Definitions.Def_BKAbsorption_defs
import Theorems.Thm_BKAbsorption_cyclic_iff_subpower
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
Barto–Kozik, Claim 4.5 (general form): cyclic terms lift through a congruence.
Uses Lemma 4.4 (`BKAbsorption.cyclic_iff_subpower`, a proved platform theorem) for `A` and for the
block subalgebra.
-/

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Fin.CommRing

namespace BKAbsorption

namespace C45

variable {L : FirstOrder.Language.{u₁, v₁}} {A : Type w₁} [L.Structure A]

/-- Subpowers are closed under term operations applied coordinatewise. -/
theorem subpower_realize {k : ℕ} {R : Set (Fin k → A)} (hR : IsSubpower L R) {α : Type*}
    (t : L.Term α) (x : α → Fin k → A) (hx : ∀ i, x i ∈ R) :
    (fun j => t.realize (fun i => x i j)) ∈ R := by
  induction t with
  | var i => exact hx i
  | func f ts ih =>
    simp only [Term.realize]
    exact hR _ f (fun l j => (ts l).realize (fun i => x i j)) ih

/-- Cyclic relations are closed under all cyclic shifts. -/
theorem shift_mem {m : ℕ} {R : Set (Fin (m + 1) → A)} (hcyc : IsCyclicRel R)
    {a : Fin (m + 1) → A} (ha : a ∈ R) : ∀ i : Fin (m + 1), (fun j => a (j + i)) ∈ R := by
  have key : ∀ n : ℕ, (fun j => a (j + (n : Fin (m + 1)))) ∈ R := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      have h := hcyc _ ih
      convert h using 1
      funext j
      show a (j + ((n + 1 : ℕ) : Fin (m + 1))) = a (finRotate (m + 1) j + (n : Fin (m + 1)))
      rw [finRotate_succ_apply, Nat.cast_succ]
      congr 1; ring
  intro i
  simpa using key i.val

theorem main [L.IsAlgebraic] [Finite A] (hid : IsIdempotent L A)
    (k : ℕ) (hk : 2 ≤ k) (r : A → A → Prop) (hr : Equivalence r)
    (hcomp : ∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
      r (funMap f x) (funMap f y))
    (hquot : ∃ t : L.Term (Fin k), ∀ x : Fin k → A,
      r (t.realize x) (t.realize (x ∘ finRotate k)))
    (hblock : ∀ C : L.Substructure A, (∃ a, (C : Set A) = {x | r x a}) →
      HasCyclicTermOp L C k) :
    HasCyclicTermOp L A k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [cyclic_iff_subpower hid (m + 1) hk]
  rintro R ⟨a, ha⟩ hRsub hRcyc
  obtain ⟨t, ht⟩ := hquot
  -- `b_j = t(σ^j a)` lies in `R`, and all its entries are `r`-related
  let b : Fin (m + 1) → A := fun j => t.realize (fun i => a (j + i))
  have hbR : b ∈ R :=
    subpower_realize hRsub t (fun i j => a (j + i)) (fun i => shift_mem hRcyc ha i)
  have hstep : ∀ j : Fin (m + 1), r (b (j + 1)) (b j) := by
    intro j
    have h := ht (fun i => a (j + i))
    have e : ((fun i => a (j + i)) ∘ finRotate (m + 1)) = fun i => a (j + 1 + i) := by
      funext i
      simp only [Function.comp, finRotate_succ_apply]
      congr 1; ring
    rw [e] at h
    exact hr.symm h
  have hall : ∀ n : ℕ, r (b (n : Fin (m + 1))) (b 0) := by
    intro n
    induction n with
    | zero => simpa using hr.refl (b 0)
    | succ n ih =>
      rw [Nat.cast_succ]
      exact hr.trans (hstep _) ih
  have hall' : ∀ j, r (b j) (b 0) := fun j => by simpa using hall j.val
  -- the block of `b 0` is a subalgebra with a cyclic term
  let C : L.Substructure A :=
    { carrier := {x | r x (b 0)}
      fun_mem := fun {n} f => by
        intro x hx
        have h := hcomp n f x (fun _ => b 0) hx
        rw [hid n f (b 0)] at h
        exact h }
  have hC := hblock C ⟨b 0, rfl⟩
  have hidC : IsIdempotent L C := fun n f c => Subtype.ext (hid n f (c : A))
  obtain ⟨c, hc⟩ := (cyclic_iff_subpower hidC (m + 1) hk).1 hC
    {y | (fun j => (y j : A)) ∈ R} ⟨fun j => ⟨b j, hall' j⟩, hbR⟩
    (fun n f x hx => hRsub n f (fun i j => (x i j : A)) hx) (fun y hy => hRcyc _ hy)
  exact ⟨c, hc⟩

end C45

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁}
    [L.Structure A] [Finite A] (hid : IsIdempotent L A)
    (k : ℕ) (hk : 2 ≤ k) (r : A → A → Prop) (hr : Equivalence r)
    (hcomp : ∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
      r (Structure.funMap f x) (Structure.funMap f y))
    (hquot : ∃ t : L.Term (Fin k), ∀ x : Fin k → A,
      r (t.realize x) (t.realize (x ∘ finRotate k)))
    (hblock : ∀ C : L.Substructure A, (∃ a, (C : Set A) = {x | r x a}) →
      HasCyclicTermOp L C k) :
    HasCyclicTermOp L A k :=
  C45.main hid k hk r hr hcomp hquot hblock
