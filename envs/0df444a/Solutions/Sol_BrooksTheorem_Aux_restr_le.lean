-- Prove2me | solution 1 for BrooksTheorem.Aux.restr_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:36:17.666642+00:00
-- url     : https://prove2.me/submissions/bb7243c2-1998-4d55-903b-22c54ae02d8a

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
namespace BrooksTheorem.Aux
theorem _root_.solution (H : SimpleGraph V) (S : Set V) : restr H S ≤ H := fun _ _ h => h.1
end BrooksTheorem.Aux
