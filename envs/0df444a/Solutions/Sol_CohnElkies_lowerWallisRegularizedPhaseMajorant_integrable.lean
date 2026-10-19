-- Prove2me | solution 1 for CohnElkies.lowerWallisRegularizedPhaseMajorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/b36aad20-da83-4026-817e-d570e8899aa0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerWallisPhaseTail_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    IntegrableOn (lowerWallisRegularizedPhaseMajorant u) (Ioi 0) := by
  have hnear :
      IntegrableOn (lowerWallisRegularizedPhaseMajorant u)
        (Ioc (0 : ℝ) 1) := by
    have hconstant :
        IntegrableOn (fun _ : ℝ => |u| + 2)
          (Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    apply hconstant.congr_fun _ measurableSet_Ioc
    intro t ht
    simp [lowerWallisRegularizedPhaseMajorant, ht.2]
  have hfar :
      IntegrableOn (lowerWallisRegularizedPhaseMajorant u)
        (Ioi (1 : ℝ)) := by
    apply lowerWallisPhaseTail_integrable.congr_fun _
      measurableSet_Ioi
    intro t ht
    simp [lowerWallisRegularizedPhaseMajorant,
      not_le.mpr (show 1 < t from ht)]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hnear.union hfar
end CohnElkies
