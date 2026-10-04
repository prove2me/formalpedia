-- Prove2me | solution 1 for CookPvsNP.stack_specification_seq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:45.370574+00:00
-- url     : https://prove2.me/submissions/b59935a5-89e7-4680-805d-2c792c87bc36

import Definitions.Def_CookPvsNP_StackSpecification

set_option autoImplicit false
open CookPvsNP

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p q : StackProg K A) (f g : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hq : StackImplements R q g d) :
    StackImplements R (p.seq q) (g ∘ f) (fun s => c s + 1 + d (f s)) := by
  intro s l hr
  obtain ⟨n, l', hn, he, hr'⟩ := hp s l hr
  obtain ⟨m, l'', hm, he', hr''⟩ := hq (f s) l' hr'
  exact ⟨n + 1 + m, l'', by dsimp only; omega, he.seq he', hr''⟩

#print axioms solution
