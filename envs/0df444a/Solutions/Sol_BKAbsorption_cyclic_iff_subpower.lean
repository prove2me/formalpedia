-- Prove2me | solution 1 for BKAbsorption.cyclic_iff_subpower
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T17:38:14.399318+00:00
-- url     : https://prove2.me/submissions/f0818cc4-48a9-4bda-86bf-fa74351ac0d1

import Definitions.Def_BKAbsorption_defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
Barto–Kozik, Lemma 4.4 (from Barto–Kozik–Maróti–Niven): a finite idempotent algebra has a
`k`-ary cyclic term operation iff every nonempty cyclic subuniverse of `A^k` contains a constant
tuple.  We write `k = m + 1` and use the additive group `Fin (m + 1)`, so the cyclic shift is
`x ↦ fun j => x (j + 1)` (`finRotate_succ_apply`).
-/

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Fin.CommRing

namespace BKAbsorption

namespace L44

variable {L : FirstOrder.Language.{u₁, v₁}} {A : Type w₁} [L.Structure A]

/-- Term operations of an idempotent algebra are idempotent. -/
theorem realize_const (hid : IsIdempotent L A) {α : Type*} (t : L.Term α) (a : A) :
    t.realize (fun _ => a) = a := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [show (fun i => (ts i).realize fun _ => a) = fun _ => a from funext ih]
    exact hid _ f a

/-- Subpowers are closed under coordinatewise term operations. -/
theorem subpower_realize {k : ℕ} {R : Set (Fin k → A)} (hR : IsSubpower L R) {α : Type*}
    (t : L.Term α) (x : α → Fin k → A) (hx : ∀ i, x i ∈ R) :
    (fun j => t.realize (fun i => x i j)) ∈ R := by
  induction t with
  | var i => exact hx i
  | func f ts ih =>
    simp only [Term.realize]
    exact hR _ f (fun l j => (ts l).realize (fun i => x i j)) ih

/-- All cyclic shifts of a member of a cyclic relation are members. -/
theorem shift_mem {m : ℕ} {R : Set (Fin (m + 1) → A)} (hcyc : IsCyclicRel R) {a : Fin (m + 1) → A}
    (ha : a ∈ R) : ∀ i : Fin (m + 1), (fun j => a (j + i)) ∈ R := by
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

/-- Forward direction: a cyclic term sends the shifts of `a` to a constant tuple. -/
theorem forward {m : ℕ} (h : HasCyclicTermOp L A (m + 1)) {R : Set (Fin (m + 1) → A)}
    (hne : R.Nonempty) (hR : IsSubpower L R) (hcyc : IsCyclicRel R) :
    ∃ a : A, (fun _ => a) ∈ R := by
  obtain ⟨t, -, ht⟩ := h
  obtain ⟨a, ha⟩ := hne
  have hmem := subpower_realize hR t (fun i j => a (j + i)) (shift_mem hcyc ha)
  have hc : ∀ j : Fin (m + 1),
      t.realize (fun i => a (j + 1 + i)) = t.realize (fun i => a (j + i)) := by
    intro j
    rw [ht (fun i => a (j + i))]
    congr 1; funext i
    simp only [Function.comp_apply, finRotate_succ_apply]
    congr 1; ring
  have hconst : ∀ n : ℕ, t.realize (fun i => a ((n : Fin (m + 1)) + i)) =
      t.realize (fun i => a (0 + i)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hc, ih]
  refine ⟨t.realize (fun i => a (0 + i)), ?_⟩
  convert hmem using 1
  funext j
  have := hconst j.val
  simp only [Fin.cast_val_eq_self] at this
  exact this.symm

variable (L) in
/-- `S(t)`: tuples on whose cyclic shifts `t` is constant. -/
def S {m : ℕ} (t : L.Term (Fin (m + 1))) : Set (Fin (m + 1) → A) :=
  {x | ∀ i : Fin (m + 1), t.realize (fun j => x (j + i)) = t.realize x}

/-- The key step of the converse: if `S(t) ≠ A^k`, some `r` has `S(t) ⊊ S(r)`. -/
theorem key_step (hid : IsIdempotent L A) {m : ℕ}
    (hall : ∀ R : Set (Fin (m + 1) → A), R.Nonempty → IsSubpower L R → IsCyclicRel R →
      ∃ a : A, (fun _ => a) ∈ R)
    (t : L.Term (Fin (m + 1))) (hS : S L (A := A) t ≠ Set.univ) :
    ∃ r : L.Term (Fin (m + 1)), S L (A := A) t ⊂ S L r := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ S L t := by
    by_contra h
    push_neg at h
    exact hS (Set.eq_univ_of_forall h)
  obtain ⟨b, hb⟩ : ∃ b : Fin (m + 1) → A, ∀ j, b j = t.realize (fun l => a (l + j)) :=
    ⟨_, fun _ => rfl⟩
  -- `C = Sg(b, σb, …)`, described by terms
  let C : Set (Fin (m + 1) → A) :=
    {c | ∃ s : L.Term (Fin (m + 1)), c = fun j => s.realize (fun i => b (j + i))}
  have hCne : C.Nonempty := ⟨_, Term.var 0, rfl⟩
  have hCsub : IsSubpower L C := by
    intro n f x hx
    choose s hs using hx
    refine ⟨Term.func f s, ?_⟩
    funext j
    simp only [Term.realize]
    congr 1; funext i; rw [hs i]
  have hCcyc : IsCyclicRel C := by
    rintro c ⟨s, rfl⟩
    refine ⟨s.relabel (fun i => 1 + i), ?_⟩
    funext j
    simp only [Function.comp_apply, finRotate_succ_apply, Term.realize_relabel]
    congr 1; funext i
    simp only [Function.comp_apply]
    congr 1; ring
  obtain ⟨e, s, hs⟩ := hall C hCne hCsub hCcyc
  have hse : ∀ j, s.realize (fun i => b (j + i)) = e := fun j => (congrFun hs j).symm
  let r : L.Term (Fin (m + 1)) := s.subst (fun i => t.relabel (fun l => l + i))
  have hr : ∀ (x : Fin (m + 1) → A) (j : Fin (m + 1)), r.realize (fun l => x (l + j)) =
      s.realize (fun i => t.realize (fun l => x (l + i + j))) := by
    intro x j
    simp only [r, Term.realize_subst, Term.realize_relabel, Function.comp_def]
  have hsub : S L (A := A) t ⊆ S L r := by
    intro x hx
    have h1 : ∀ j, r.realize (fun l => x (l + j)) = t.realize x := by
      intro j
      rw [hr x j]
      have h2 : (fun i => t.realize (fun l => x (l + i + j))) = fun _ => t.realize x := by
        funext i
        simp only [add_assoc]
        exact hx (i + j)
      rw [h2, realize_const hid]
    intro i
    rw [h1 i]
    have h0 := h1 0
    simp only [add_zero] at h0
    exact h0.symm
  refine ⟨r, (Set.ssubset_iff_of_subset hsub).2 ⟨a, ?_, ha⟩⟩
  have h1 : ∀ j, r.realize (fun l => a (l + j)) = e := by
    intro j
    rw [hr a j, ← hse j]
    congr 1; funext i
    rw [hb]
    congr 1; funext l
    congr 1; ring
  intro i
  rw [h1 i]
  have h0 := h1 0
  simp only [add_zero] at h0
  exact h0.symm

theorem main [Finite A] (hid : IsIdempotent L A) (k : ℕ) (hk : 2 ≤ k) :
    HasCyclicTermOp L A k ↔
      ∀ R : Set (Fin k → A), R.Nonempty → IsSubpower L R → IsCyclicRel R →
        ∃ a : A, (fun _ => a) ∈ R := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  constructor
  · intro h R hne hR hcyc
    exact forward h hne hR hcyc
  · intro hall
    have aux : ∀ (n : ℕ) (t : L.Term (Fin (m + 1))), (S L (A := A) t)ᶜ.ncard = n →
        ∃ r : L.Term (Fin (m + 1)), S L (A := A) r = Set.univ := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro t hn
      by_cases hS : S L (A := A) t = Set.univ
      · exact ⟨t, hS⟩
      · obtain ⟨r, hr⟩ := key_step hid hall t hS
        exact ih _ (hn ▸ Set.ncard_lt_ncard (compl_lt_compl_iff_lt.2 hr)) r rfl
    obtain ⟨r, hr⟩ := aux _ (Term.var 0) rfl
    refine ⟨r, fun a => realize_const hid r a, fun x => ?_⟩
    have hx : x ∈ S L (A := A) r := hr ▸ Set.mem_univ x
    have h1 := hx 1
    rw [← h1]
    congr 1
    funext j
    simp

end L44

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁}
    [L.Structure A] [Finite A] (hid : IsIdempotent L A) (k : ℕ) (hk : 2 ≤ k) :
    HasCyclicTermOp L A k ↔
      ∀ R : Set (Fin k → A), R.Nonempty → IsSubpower L R → IsCyclicRel R →
        ∃ a : A, (fun _ => a) ∈ R :=
  L44.main hid k hk
