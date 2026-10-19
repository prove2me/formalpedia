-- Prove2me | solution 1 for CohnElkies.inverseQuadraticAbs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/53df3f73-fc97-42cd-9512-d77e194788d2

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable (fun S : ℝ => 1 / (1 + |S|) ^ 2) := by
  have hbase := integrable_one_add_norm
    (E := ℝ) (μ := volume) (r := (2 : ℝ))
      (by norm_num)
  convert! hbase using 1
  ext S
  rw [Real.norm_eq_abs,
    Real.rpow_neg (by positivity)]
  simp [one_div]
end CohnElkies
