-- Prove2me | solution 1 for C6BipartiteDomination.mem_paper10SpecialQSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:54:59.787247+00:00
-- url     : https://prove2.me/submissions/3346230e-e661-481b-9a01-09adfb22d314

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) :
    q ∈ paper10SpecialQSet G hCan hmax ↔ IsPaper10SpecialQ G hCan hmax q := by
  classical
  simp [paper10SpecialQSet]
end C6BipartiteDomination
