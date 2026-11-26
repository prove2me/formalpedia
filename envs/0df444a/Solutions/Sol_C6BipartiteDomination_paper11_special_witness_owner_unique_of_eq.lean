-- Prove2me | solution 1 for C6BipartiteDomination.paper11_special_witness_owner_unique_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:25.367937+00:00
-- url     : https://prove2.me/submissions/42f6275d-9e7d-4f3f-8e7d-71f668d47e6d

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11_special_witness_owner_unique

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q₁ q₂ : V}
    (hq : q₁ = q₂)
    (d₁ : Paper10SpecialWitness G hCan hmax q₁)
    (d₂ : Paper10SpecialWitness G hCan hmax q₂) : d₁.u = d₂.u := by
  subst q₂
  exact paper11_special_witness_owner_unique G hCan hmax d₁ d₂
end C6BipartiteDomination
