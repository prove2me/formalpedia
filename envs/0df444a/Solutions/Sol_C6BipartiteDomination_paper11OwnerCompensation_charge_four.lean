-- Prove2me | solution 1 for C6BipartiteDomination.paper11OwnerCompensation_charge_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:54.363388+00:00
-- url     : https://prove2.me/submissions/4048d26f-7535-41b0-aa61-c0c6e750d17a

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_mem_supportX
import Theorems.Thm_C6BipartiteDomination_paper9_shared_external_charge_eq_four


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u q : V}
    (huB : u ∈ BPart G D)
    (hq : q ∈ paper11OwnerCompensation G D hCan hmax u) :
    externalCharge G D q = 4 := by
  classical
  obtain ⟨w, hw, hq⟩ := Finset.mem_biUnion.mp hq
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  exact paper9_shared_external_charge_eq_four G hX huB hq
end C6BipartiteDomination
