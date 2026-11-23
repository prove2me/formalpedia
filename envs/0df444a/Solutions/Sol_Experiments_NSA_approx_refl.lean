-- Prove2me | solution 1 for Experiments.NSA.approx_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:21:15.293676+00:00
-- url     : https://prove2.me/submissions/3fcbf0fa-95a1-4c33-b6ca-486997f4445f

import Mathlib
import Definitions.Def_Experiments_Ultrapower
import Theorems.Thm_Experiments_NSA_approx_coe

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Experiments.NSA
theorem _root_.solution (x : Hyp E) : x ≈ₕ x := by
  induction x using Germ.inductionOn with
  | h u => exact approx_coe.mpr (by simp)
end Experiments.NSA
