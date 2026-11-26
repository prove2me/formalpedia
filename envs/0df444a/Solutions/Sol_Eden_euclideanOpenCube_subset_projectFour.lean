-- Prove2me | solution 1 for Eden.euclideanOpenCube_subset_projectFour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:51.655965+00:00
-- url     : https://prove2.me/submissions/7e48197f-100f-4ec5-b224-be88b1558249

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
import Theorems.Thm_Eden_projectFour_embedFour
import Theorems.Thm_Eden_embedFour_mem_attractor

set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden
namespace Eden
theorem _root_.solution :
    euclideanOpenCube 4 ⊆ projectFour '' attractor := by
  intro x hx
  exact ⟨embedFour x, embedFour_mem_attractor hx, projectFour_embedFour x⟩
end Eden
