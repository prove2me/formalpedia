-- Prove2me | solution 1 for Experiments.NSA.transfer_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:45.676566+00:00
-- url     : https://prove2.me/submissions/e6e4e022-7aec-48a4-86b6-b53b4ab82482

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution {f g : α → ℝ} {s : Set α} (h : ∀ x ∈ s, f x ≤ g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ ≤ ext g ξ := by
  induction ξ using Germ.inductionOn with
  | h u => exact Germ.coe_le.mpr ((Germ.liftPred_coe.mp hξ).mono fun n => h _)
end Experiments.NSA
