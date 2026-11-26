-- Prove2me | solution 1 for C6BipartiteDomination.paper10SpecialEndpoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:38.885708+00:00
-- url     : https://prove2.me/submissions/f4723b0b-879f-466d-a9f2-9b76633ebe31

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
import Theorems.Thm_C6BipartiteDomination_mem_supportX


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (hq : IsPaper10SpecialQ G hCan hmax q) :
    ∃ z ∈ Z0Part G D, paper10SpecialEndpoint G hCan hmax q = some z := by
  let data := Classical.choice hq
  have hz0 : data.z ∈ Z0Part G D :=
    (mem_supportX G D data.w₁ data.z).mp data.zSupport₁ |>.1
  refine ⟨data.z, hz0, ?_⟩
  simp [paper10SpecialEndpoint, hq, data]
end C6BipartiteDomination
