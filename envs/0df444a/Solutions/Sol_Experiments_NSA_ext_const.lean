-- Prove2me | solution 1 for Experiments.NSA.ext_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:58.28802+00:00
-- url     : https://prove2.me/submissions/0bd35a7a-b550-4cab-ba20-54328e382afb

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution (ξ : Hyp α) (c : β) : ext (fun _ => c) ξ = std c :=
  Germ.inductionOn ξ fun _ => rfl
end Experiments.NSA
