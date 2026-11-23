-- Prove2me | solution 1 for Experiments.NSA.ext_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:02:59.954122+00:00
-- url     : https://prove2.me/submissions/80b79df8-7b13-48e3-b985-b9aabaeed403

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution [Mul β] (f g : α → β) (ξ : Hyp α) :
    ext (fun x => f x * g x) ξ = ext f ξ * ext g ξ :=
  Germ.inductionOn ξ fun _ => rfl
end Experiments.NSA
