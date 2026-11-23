-- Prove2me | solution 1 for Experiments.NSA.transfer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:53.728034+00:00
-- url     : https://prove2.me/submissions/c2b3819c-4746-44ce-adb7-f8de493f3d93

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution {f g : α → β} {s : Set α} (h : ∀ x ∈ s, f x = g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ = ext g ξ := by
  induction ξ using Germ.inductionOn with
  | h u => exact Germ.coe_eq.mpr ((Germ.liftPred_coe.mp hξ).mono fun n => h _)
end Experiments.NSA
