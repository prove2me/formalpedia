-- Prove2me | solution 1 for CookPvsNP.stack_specification_budget
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:47.505866+00:00
-- url     : https://prove2.me/submissions/eb36cc97-1911-4438-a2d8-16365fb0672b

import Definitions.Def_CookPvsNP_StackSpecification

set_option autoImplicit false
open CookPvsNP

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (f : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hd : ∀ s, c s ≤ d s) :
    StackImplements R p f d := by
  intro s l hr
  obtain ⟨n, l', hn, he, hr'⟩ := hp s l hr
  exact ⟨n, l', hn.trans (hd s), he, hr'⟩

#print axioms solution
