-- Prove2me | solution 1 for Experiments.NSA.eq_of_std_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:21:44.07431+00:00
-- url     : https://prove2.me/submissions/ef8ca72a-72f6-41a6-80e3-7e44731661ee

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
theorem _root_.solution {a b : E} (h : std a ≈ₕ std b) : a = b :=
  tendsto_nhds_unique tendsto_const_nhds (approx_std_coe.mp h)
end Experiments.NSA
