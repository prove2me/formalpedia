-- Prove2me | solution 1 for Experiments.NSA.Approx.sub_std
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:21:34.973488+00:00
-- url     : https://prove2.me/submissions/bbdf26ab-a1f0-4d38-bd60-8206a7a6fc04

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
namespace Approx
theorem _root_.solution {x y : Hyp E} {a b : E} (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) :
    x - y ≈ₕ std (a - b) := by
  induction x, y using Germ.inductionOn₂ with
  | h u v => exact approx_std_coe.mpr ((approx_std_coe.mp hx).sub (approx_std_coe.mp hy))
end Approx
end Experiments.NSA
