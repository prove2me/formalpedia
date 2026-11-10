-- Prove2me | solution 1 for BKAbsorption.cyclic_term_prime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T16:15:01.786208+00:00
-- url     : https://prove2.me/submissions/3e9dad22-9cd5-41da-833a-85e6bece1bf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BKAbsorption_defs
import Theorems.Thm_BKAbsorption_cyclic_of_congruence
import Theorems.Thm_BKAbsorption_cyclic_simple_core
import Mathlib.ModelTheory.Quotients
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.EquivFin

/-!
Barto–Kozik, Theorem 4.2, by induction on `|A|` (minimal counterexample), reduced to
* `cyclic_of_congruence` (Claim 4.5): cyclic terms lift from `A/θ` and the `θ`-blocks to `A`;
* `cyclic_simple_core` (Claims 4.6–4.14): the case of a simple `A` all of whose proper
  subalgebras have `p`-ary cyclic terms.
-/

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

namespace BKAbsorption

namespace T42

variable {L : FirstOrder.Language.{u₁, v₁}}

theorem realize_hom {M N : Type*} [L.Structure M] [L.Structure N] (φ : M → N)
    (hφ : ∀ (n : ℕ) (f : L.Functions n) (x : Fin n → M), φ (funMap f x) = funMap f (φ ∘ x))
    {α : Type*} (t : L.Term α) (a : α → M) : φ (t.realize a) = t.realize (φ ∘ a) := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [hφ]
    congr 1
    funext i
    exact ih i

theorem coe_realize_sub {M : Type*} [L.Structure M] (S : L.Substructure M) {α : Type*}
    (t : L.Term α) (a : α → S) : ((t.realize a : S) : M) = t.realize (fun i => (a i : M)) :=
  realize_hom (L := L) Subtype.val (fun _ _ _ => rfl) t a

/-- Subalgebras of an algebra in the Taylor variety of `T` lie in it. -/
theorem taylor_sub {M : Type*} [L.Structure M] {T : TaylorDatum L} (hM : IsTaylorAlg T M)
    (S : L.Substructure M) : IsTaylorAlg T S := by
  refine ⟨fun n f a => Subtype.ext (hM.1 n f (a : M)), fun j x y => Subtype.ext ?_⟩
  rw [coe_realize_sub, coe_realize_sub]
  have e : ∀ b : Bool, ((cond b y x : S) : M) = cond b (y : M) (x : M) := by
    intro b; cases b <;> rfl
  simp only [e]
  exact hM.2 j x y

variable [L.IsAlgebraic]

/-- Quotients of an algebra in the Taylor variety of `T` lie in it. -/
theorem taylor_quot {M : Type*} [L.Structure M] {T : TaylorDatum L} (hM : IsTaylorAlg T M)
    (s : Setoid M) [ps : L.Prestructure s] (hps : ps.toStructure = ‹L.Structure M›) :
    IsTaylorAlg T (Quotient s) := by
  subst hps
  refine ⟨fun n f q => ?_, fun j q₁ q₂ => ?_⟩
  · induction q using Quotient.inductionOn with
    | h a =>
      have := funMap_quotient_mk' (L := L) s f (fun _ => a)
      rw [this, hM.1 n f a]
  · induction q₁, q₂ using Quotient.inductionOn₂ with
    | h x y =>
      have e : ∀ b : Bool, (cond b (⟦y⟧ : Quotient s) ⟦x⟧) = ⟦cond b y x⟧ := by
        intro b; cases b <;> rfl
      simp only [e]
      rw [Term.realize_quotient_mk', Term.realize_quotient_mk', hM.2 j x y]

theorem main (T : TaylorDatum L) (p : ℕ) (hp : p.Prime) :
    ∀ (n : ℕ) (A : Type w₁) [L.Structure A] [Finite A], Nat.card A = n → IsTaylorAlg T A →
      Nat.card A < p → HasCyclicTermOp L A p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ hn hA hpA
  have IH : ∀ (B : Type w₁) [L.Structure B] [Finite B], Nat.card B < Nat.card A →
      IsTaylorAlg T B → HasCyclicTermOp L B p :=
    fun B _ _ hB hTB => ih _ (hn ▸ hB) B rfl hTB (hB.trans hpA)
  by_cases hs : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (funMap f x) (funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b
  · refine cyclic_simple_core T hA p hp hpA hs (fun S hS => ?_)
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 hS
    exact IH S (Finite.card_subtype_lt (p := fun y => y ∈ S) hx) (taylor_sub hA S)
  obtain ⟨r, hr, hc, h⟩ : ∃ r : A → A → Prop, Equivalence r ∧
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (funMap f x) (funMap f y)) ∧ ¬((∀ a b, r a b → a = b) ∨ ∀ a b, r a b) := by
    by_contra hcon
    exact hs (fun r hr hc => by_contra fun h => hcon ⟨r, hr, hc, h⟩)
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, r a b ∧ a ≠ b := by
    by_contra hh
    exact h1 (fun a b hab => by_contra fun hne => hh ⟨a, b, hab, hne⟩)
  obtain ⟨c, d, hcd⟩ : ∃ c d, ¬ r c d := by
    by_contra hh
    exact h2 (fun a b => by_contra fun hn => hh ⟨a, b, hn⟩)
  let s : Setoid A := ⟨r, hr⟩
  let ps : L.Prestructure s :=
    { toStructure := ‹_›
      fun_equiv := fun {n} {f} x y hxy => hc n f x y hxy
      rel_equiv := fun {n} {r} _ _ _ => isEmptyElim r }
  -- the quotient `A / r` is smaller, hence has a cyclic term
  have hcardQ : Nat.card (Quotient s) < Nat.card A := by
    have := Fintype.ofFinite A
    have := Fintype.ofFinite (Quotient s)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_surjective_not_injective (Quotient.mk s) Quotient.mk_surjective
      (fun hinj => hne (hinj (Quotient.sound hab)))
  obtain ⟨t, -, ht⟩ := IH (Quotient s) hcardQ (taylor_quot hA s rfl)
  have hquot : ∃ t : L.Term (Fin p), ∀ x : Fin p → A,
      r (t.realize x) (t.realize (x ∘ finRotate p)) := by
    refine ⟨t, fun x => ?_⟩
    have h := ht (fun i => ⟦x i⟧)
    have e : (fun i => (⟦x i⟧ : Quotient s)) ∘ finRotate p = fun i => ⟦(x ∘ finRotate p) i⟧ :=
      rfl
    rw [e, Term.realize_quotient_mk', Term.realize_quotient_mk'] at h
    exact Quotient.exact h
  refine cyclic_of_congruence hA.1 p hp.two_le r hr hc hquot (fun C ⟨e, he⟩ => ?_)
  -- every block is a proper subalgebra
  have hx : ∃ x, x ∉ (C : Set A) := by
    by_contra hh
    have hall : ∀ x, r x e := fun x => by
      have : x ∈ (C : Set A) := by_contra fun hn => hh ⟨x, hn⟩
      rw [he] at this
      exact this
    exact hcd (hr.trans (hall c) (hr.symm (hall d)))
  obtain ⟨x, hx⟩ := hx
  exact IH C (Finite.card_subtype_lt (p := fun y => y ∈ C) hx) (taylor_sub hA C)

end T42

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁}
    [L.Structure A] [Finite A] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (p : ℕ) (hp : p.Prime) (hpA : Nat.card A < p) :
    HasCyclicTermOp L A p :=
  T42.main T p hp _ A rfl hA hpA
