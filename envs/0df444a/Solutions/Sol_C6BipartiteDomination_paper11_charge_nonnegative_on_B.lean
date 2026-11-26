-- Prove2me | solution 1 for C6BipartiteDomination.paper11_charge_nonnegative_on_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:25.659643+00:00
-- url     : https://prove2.me/submissions/8a25f6e7-9b62-4841-b625-f12851f4c685

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper9_sCharge_add_xCharge_le_three


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ BPart G D) :
    0 ≤ vertexCharge G D u := by
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax hu
  have hbudgetZ : (sCharge G D u : ℤ) + (xCharge G D u : ℤ) ≤ 3 := by
    exact_mod_cast hbudget
  have hx : 0 ≤ (xCharge G D u : ℤ) := by positivity
  unfold vertexCharge
  nlinarith
end C6BipartiteDomination
