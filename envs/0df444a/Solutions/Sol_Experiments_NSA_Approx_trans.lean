-- Prove2me | solution 1 for Experiments.NSA.Approx.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:48.074004+00:00
-- url     : https://prove2.me/submissions/e4d1b5b4-4df8-4061-8569-c126c735d993

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
theorem _root_.solution {x y z : Hyp E} (hxy : x ≈ₕ y) (hyz : y ≈ₕ z) : x ≈ₕ z := by
  induction x, y, z using Germ.inductionOn₃ with
  | H u v w => exact approx_coe.mpr (by simpa using (approx_coe.mp hxy).add (approx_coe.mp hyz))
end Approx
end Experiments.NSA
