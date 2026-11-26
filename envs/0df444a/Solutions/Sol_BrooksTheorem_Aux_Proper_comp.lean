-- Prove2me | solution 1 for BrooksTheorem.Aux.Proper.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:20.740797+00:00
-- url     : https://prove2.me/submissions/167dbe9a-1128-4132-b308-1da8dad9048b

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
theorem _root_.solution {k : ℕ} {H : SimpleGraph V} {f : V → Fin k} (hf : Proper H f)
    (σ : Equiv.Perm (Fin k)) : Proper H (σ ∘ f) :=
  fun u v h e => hf u v h (σ.injective e)
end Proper
end BrooksTheorem.Aux
