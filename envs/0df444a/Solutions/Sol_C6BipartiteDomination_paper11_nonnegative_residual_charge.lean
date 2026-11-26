-- Prove2me | solution 1 for C6BipartiteDomination.paper11_nonnegative_residual_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:30.849914+00:00
-- url     : https://prove2.me/submissions/499b4050-ed0e-462b-b024-861206954ce0

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    0 ≤ ∑ q ∈ paper11NonnegativeSupports G D \
        paper11AllCompensation G D hCan hmax, externalCharge G D q := by
  apply Finset.sum_nonneg
  intro q hq
  have hP := (Finset.mem_sdiff.mp hq).1
  have hS := (Finset.mem_sdiff.mp hP).1
  have hnotneg := (Finset.mem_sdiff.mp hP).2
  have hnotN : q ∉ paper11NegativeSupports G D := by
    intro hN
    exact hnotneg hN
  have hnotlt : ¬ externalCharge G D q < 0 := by
    intro hlt
    exact hnotN (Finset.mem_filter.mpr ⟨hS, hlt⟩)
  omega
end C6BipartiteDomination
