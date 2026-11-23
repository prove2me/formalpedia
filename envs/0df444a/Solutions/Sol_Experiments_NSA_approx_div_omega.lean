-- Prove2me | solution 1 for Experiments.NSA.approx_div_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:23:52.133547+00:00
-- url     : https://prove2.me/submissions/a579aafc-db7e-4627-81ed-3f6509c448d8

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
theorem _root_.solution (c : ℝ) : ext (fun n : ℕ => c / (n + 1 : ℝ)) ω ≈ₕ std 0 := by
  refine approx_std_coe.mpr (Tendsto.mono_left ?_ Nat.hyperfilter_le_atTop)
  simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
end Experiments.NSA
