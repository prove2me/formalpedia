-- Prove2me | solution 1 for C6BipartiteDomination.paper11_special_witness_owner_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:29.12288+00:00
-- url     : https://prove2.me/submissions/78f1237a-7204-48e0-8ab8-f8b1a7fa3258

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11_compensation_unique_B_owner
import Theorems.Thm_C6BipartiteDomination_mem_supportX


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (d₁ d₂ : Paper10SpecialWitness G hCan hmax q) : d₁.u = d₂.u := by
  have hX₁ : supportX G D d₁.w₁ ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D d₁.w₁ z).mp hz |>.1
  have hX₂ : supportX G D d₂.w₁ ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D d₂.w₁ z).mp hz |>.1
  exact paper11_compensation_unique_B_owner G hX₁ hX₂ d₁.uB d₂.uB
    d₁.qShared₁ d₂.qShared₁
end C6BipartiteDomination
