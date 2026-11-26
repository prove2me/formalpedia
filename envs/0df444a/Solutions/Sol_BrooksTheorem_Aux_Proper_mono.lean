-- Prove2me | solution 1 for BrooksTheorem.Aux.Proper.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:34:04.55244+00:00
-- url     : https://prove2.me/submissions/9fc48eb9-4c83-4187-ad44-37b2c29a87e6

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
namespace Proper
theorem _root_.solution {k : ℕ} {H H' : SimpleGraph V} {f : V → Fin k} (hf : Proper H f)
    (hle : H' ≤ H) : Proper H' f :=
  fun u v h => hf u v (hle h)
end Proper
end BrooksTheorem.Aux
