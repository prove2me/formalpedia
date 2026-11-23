-- Prove2me | solution 1 for Experiments.NSA.transfer_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:37.415867+00:00
-- url     : https://prove2.me/submissions/55374eff-7b3c-4fe9-b904-01d0190a055a

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}
namespace Experiments.NSA
theorem _root_.solution {f : α → β} {s : Set α} {t : Set β} (h : ∀ x ∈ s, f x ∈ t) {ξ : Hyp α}
    (hξ : IMem ξ s) : IMem (ext f ξ) t := by
  induction ξ using Germ.inductionOn with
  | h u => exact Germ.liftPred_coe.mpr ((Germ.liftPred_coe.mp hξ).mono fun n => h _)
end Experiments.NSA
