-- Prove2me | solution 1 for Experiments.NSA.approx_std_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:48:41.088968+00:00
-- url     : https://prove2.me/submissions/525e88d4-9c4e-4996-a9db-0cec454f8534

import Mathlib
import Definitions.Def_Experiments_Ultrapower

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Experiments.NSA
theorem _root_.solution {u : ℕ → E} {a : E} :
    (u : Hyp E) ≈ₕ std a ↔ Tendsto u (hyperfilter ℕ) (𝓝 a) :=
  tendsto_sub_nhds_zero_iff
end Experiments.NSA
