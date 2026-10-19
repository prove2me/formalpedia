-- Prove2me | solution 1 for CohnElkies.saddleSource_cubic_window_le_of_variance_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/16328c9a-acd5-4297-972c-d0bb69f7d61e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSource_cubic_window_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ V M C V₀ z T : ℝ}
    (hℓ : 0 < ℓ) (hV₀ : 0 < V₀)
    (hfloor : V₀ ≤ V)
    (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hM : M ≤ C * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (C / 6) * z ^ 3 /
        (Real.sqrt ℓ * Real.sqrt V₀) := by
  have hV : 0 < V := hV₀.trans_le hfloor
  have hbase := saddleSource_cubic_window_le
    hℓ hV hC hz hM hT
  calc
    (ℓ * M / 6) * |T| ^ 3 ≤
        (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := hbase
    _ ≤ (C / 6) * z ^ 3 / Real.sqrt (ℓ * V₀) := by
      gcongr
    _ = (C / 6) * z ^ 3 /
        (Real.sqrt ℓ * Real.sqrt V₀) := by
      rw [Real.sqrt_mul hℓ.le]
end CohnElkies
