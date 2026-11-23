-- Prove2me | solution 1 for Experiments.NSA.Approx.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:47.573928+00:00
-- url     : https://prove2.me/submissions/70cc3bee-fb2d-47a7-beb4-4326ee666c64

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
namespace Approx
theorem _root_.solution {x y : Hyp E} (h : x ≈ₕ y) : y ≈ₕ x := by
  induction x, y using Germ.inductionOn₂ with
  | h u v => exact approx_coe.mpr (by simpa using (approx_coe.mp h).neg)
end Approx
end Experiments.NSA
