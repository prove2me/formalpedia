-- Prove2me | solution 1 for Experiments.NSA.approx_zero_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:21:49.5388+00:00
-- url     : https://prove2.me/submissions/fbd50a9d-fa02-43a7-93a4-7a3e55475c17

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
theorem _root_.solution {x : Hyp E} {y : Hyp F} {k : Hyp ℝ} {c : ℝ} (hk : k ≈ₕ std c)
    (hxy : ext norm x ≤ k * ext norm y) (hy : y ≈ₕ std 0) : x ≈ₕ std 0 := by
  induction x, y, k using Germ.inductionOn₃ with
  | H u v κ =>
    refine approx_std_coe.mpr (squeeze_zero_norm' (Germ.coe_le.mp hxy) ?_)
    simpa using (approx_std_coe.mp hk).mul (approx_std_coe.mp hy).norm
end Experiments.NSA
