-- Prove2me | solution 1 for Eden.norm_initialExteriorBasisVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:26.242327+00:00
-- url     : https://prove2.me/submissions/ae7a3d2f-7972-4f47-a811-ab26661323f6

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
import Theorems.Thm_Eden_norm_exterior_map_isometry


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    ‖initialExteriorBasisVector k p s‖ = 1 := by
  rw [initialExteriorBasisVector, norm_exterior_map_isometry]
  exact (exteriorBasis k).orthonormal.norm_eq_one s
end Eden
