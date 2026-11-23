-- Prove2me | solution 1 for Experiments.NSA.approx_ext_of_continuousWithinAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:22:22.638281+00:00
-- url     : https://prove2.me/submissions/0b71f2be-4ca7-40e4-bbf1-00d77b6a3c1c

import Mathlib
import Definitions.Def_Experiments_Ultrapower
import Theorems.Thm_Experiments_NSA_approx_std_coe

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Experiments.NSA
theorem _root_.solution {f : F → E} {s : Set F} {x : F}
    (hf : ContinuousWithinAt f s x) {ξ : Hyp F} (hξs : IMem ξ s) (hξ : ξ ≈ₕ std x) :
    ext f ξ ≈ₕ std (f x) := by
  induction ξ using Germ.inductionOn with
  | h u =>
    exact approx_std_coe.mpr (hf.tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨approx_std_coe.mp hξ, Germ.liftPred_coe.mp hξs⟩))
end Experiments.NSA
