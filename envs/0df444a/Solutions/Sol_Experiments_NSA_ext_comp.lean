-- Prove2me | solution 1 for Experiments.NSA.ext_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:56.357968+00:00
-- url     : https://prove2.me/submissions/ff928cbd-8d7c-4208-8464-f6a44f156212

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution (f : β → γ) (g : α → β) (ξ : Hyp α) :
    ext f (ext g ξ) = ext (fun x => f (g x)) ξ :=
  Germ.map_map f g ξ
end Experiments.NSA
