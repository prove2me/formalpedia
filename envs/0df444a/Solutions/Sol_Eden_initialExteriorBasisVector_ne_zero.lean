-- Prove2me | solution 1 for Eden.initialExteriorBasisVector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:34:34.022178+00:00
-- url     : https://prove2.me/submissions/218a9dcd-a840-4d9a-aea5-a4dae29dd68f

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
import Theorems.Thm_Eden_norm_initialExteriorBasisVector

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    initialExteriorBasisVector k p s ≠ 0 := by
  intro h
  have hn := norm_initialExteriorBasisVector k p s
  rw [h, norm_zero] at hn
  norm_num at hn
end Eden
