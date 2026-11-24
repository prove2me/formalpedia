-- Prove2me | solution 1 for BondySimonovits.restrictGraph_walk_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:10:53.834265+00:00
-- url     : https://prove2.me/submissions/ee15d38a-a5f1-48e3-960f-625587e9eb8f

module
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Definitions.Def_BondySimonovitsLib_BSFinal

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution (H : SimpleGraph V) (Y : Set V) :
    ∀ {u v : V} (_ : (restrictGraph H Y).Walk u v), u ∈ Y → v ∈ Y := by
  intro u v p
  induction p with
  | nil => exact id
  | cons h _ ih => exact fun _ => ih (show H.Adj _ _ ∧ _ ∈ Y ∧ _ ∈ Y from h).2.2
end BondySimonovits
