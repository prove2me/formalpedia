-- Prove2me | solution 1 for CookPvsNP.stack_specification_loop
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:44.168464+00:00
-- url     : https://prove2.me/submissions/a332ed04-e3cb-4bfd-b05f-32f011c93113

import Definitions.Def_CookPvsNP_StackSpecification

set_option autoImplicit false
open CookPvsNP

private theorem loop {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (test : (K → Option A) → Bool) (f : S → S) (cost rank : S → ℕ)
    (hp : StackImplements R p f cost)
    (ht : ∀ s l, R s l → test (fun k => (l k).head?) = decide (0 < rank s))
    (hd : ∀ s, 0 < rank s → rank (f s) + 1 = rank s)
    (n : ℕ) (s : S) (l : K → List A) (hr : R s l) (hn : rank s = n) :
    ∃ t l', t ≤ stackLoopCost f cost n s ∧
      (StackProg.loop test p).Exec l l' t ∧ R ((f^[n]) s) l' := by
  induction n generalizing s l with
  | zero =>
    refine ⟨1, l, by simp [stackLoopCost], .loopFalse ?_, hr⟩
    simp [ht s l hr, hn]
  | succ n ih =>
    obtain ⟨a, l', ha, he, hrep⟩ := hp s l hr
    have hpos : 0 < rank s := by omega
    have hnext : rank (f s) = n := by have := hd s hpos; omega
    obtain ⟨b, l'', hb, he', hrep'⟩ := ih (f s) l' hrep hnext
    refine ⟨1 + a + 1 + b, l'', ?_, .loopTrue ?_ he he', ?_⟩
    · unfold stackLoopCost at hb ⊢
      rw [Finset.sum_range_succ']
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
      omega
    · simp [ht s l hr, hpos]
    · simpa only [Function.iterate_succ_apply] using hrep'

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (test : (K → Option A) → Bool) (f : S → S) (cost rank : S → ℕ)
    (hp : StackImplements R p f cost)
    (ht : ∀ s l, R s l → test (fun k => (l k).head?) = decide (0 < rank s))
    (hd : ∀ s, 0 < rank s → rank (f s) + 1 = rank s) :
    StackImplements R (StackProg.loop test p) (fun s => (f^[rank s]) s)
      (fun s => stackLoopCost f cost (rank s) s) := by
  intro s l hr
  exact loop R p test f cost rank hp ht hd (rank s) s l hr rfl

#print axioms solution
