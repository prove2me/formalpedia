-- Prove2me | solution 1 for Experiments.NSA.ext_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:02:01.351266+00:00
-- url     : https://prove2.me/submissions/efac34e6-072a-4166-b0e9-92073dc379fa

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution (ξ : Hyp α) : ext (fun x => x) ξ = ξ :=
  Germ.inductionOn ξ fun _ => rfl
end Experiments.NSA
