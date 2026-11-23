-- Prove2me | solution 1 for Experiments.NSA.approx_iff_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:21:17.283088+00:00
-- url     : https://prove2.me/submissions/1b5dfa11-7b85-407d-89b3-f1293c82f799

import Mathlib
import Definitions.Def_Experiments_Ultrapower
import Theorems.Thm_Experiments_NSA_approx_coe
import Theorems.Thm_Experiments_NSA_approx_std_coe
import Theorems.Thm_Experiments_NSA_Approx_symm
import Theorems.Thm_Experiments_NSA_Approx_trans

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Experiments.NSA
theorem _root_.solution {x y : Hyp E} : x ≈ₕ y ↔ x - y ≈ₕ std 0 := by
  induction x, y using Germ.inductionOn₂ with
  | h u v => exact approx_coe.trans (approx_std_coe (u := fun n => u n - v n)).symm
end Experiments.NSA
