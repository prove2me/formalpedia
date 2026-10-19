-- Prove2me | solution 1 for CohnElkies.sharpPackingRoot_of_sharpQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/144e3b45-8786-4653-a45e-10b09079d3d9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_packingGeometricRoot
import Theorems.Thm_CohnElkies_linearProgram_root_eq_geometric_mul_normalizedProgram_unconditional
import Theorems.Thm_CohnElkies_geometricLimit_mul_criticalRadius

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hquotient : SharpQuotientAsymptotic) :
    SharpPackingRootAsymptotic := by
  unfold SharpQuotientAsymptotic at hquotient
  unfold SharpPackingRootAsymptotic
  have hproduct := tendsto_packingGeometricRoot.mul hquotient
  rw [geometricLimit_mul_criticalRadius] at hproduct
  refine hproduct.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact
    (linearProgram_root_eq_geometric_mul_normalizedProgram_unconditional
      hd).symm
end CohnElkies
