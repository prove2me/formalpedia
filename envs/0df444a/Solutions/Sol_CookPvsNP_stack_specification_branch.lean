-- Prove2me | solution 1 for CookPvsNP.stack_specification_branch
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:46.497097+00:00
-- url     : https://prove2.me/submissions/ee40f251-19bc-4c10-b196-993987bffae7

import Definitions.Def_CookPvsNP_StackSpecification

set_option autoImplicit false
open CookPvsNP

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p q : StackProg K A) (test : (K → Option A) → Bool) (b : S → Bool)
    (f g : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hq : StackImplements R q g d)
    (hb : ∀ s l, R s l → test (fun k => (l k).head?) = b s) :
    StackImplements R (.branch test p q) (fun s => if b s then f s else g s)
      (fun s => 1 + max (c s) (d s)) := by
  intro s l hr
  cases h : b s with
  | false =>
    obtain ⟨n, l', hn, he, hr'⟩ := hq s l hr
    refine ⟨1 + n, l', ?_, .branchFalse ((hb s l hr).trans h) he, ?_⟩
    · dsimp only; have := le_max_right (c s) (d s); omega
    · simpa [h] using hr'
  | true =>
    obtain ⟨n, l', hn, he, hr'⟩ := hp s l hr
    refine ⟨1 + n, l', ?_, .branchTrue ((hb s l hr).trans h) he, ?_⟩
    · dsimp only; have := le_max_left (c s) (d s); omega
    · simpa [h] using hr'

#print axioms solution
