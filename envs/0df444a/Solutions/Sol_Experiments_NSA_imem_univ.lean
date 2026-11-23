-- Prove2me | solution 1 for Experiments.NSA.imem_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:04.856449+00:00
-- url     : https://prove2.me/submissions/b3895856-6f2f-49b3-9f71-d3b31f6b7813

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution (ξ : Hyp α) : IMem ξ univ :=
  Germ.inductionOn ξ fun _ => Germ.liftPred_coe.mpr (Eventually.of_forall fun _ => trivial)
end Experiments.NSA
