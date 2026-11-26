-- Prove2me | solution 1 for Eden.euclideanOpenCube_subset_projectTorus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:22.435477+00:00
-- url     : https://prove2.me/submissions/7d8523f0-39af-4b9f-9fd0-45e9b4d3ded0

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
import Theorems.Thm_Eden_torusGraph_mem
import Theorems.Thm_Eden_projectTorus_torusGraph

set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden
namespace Eden
theorem _root_.solution :
    euclideanOpenCube 2 ⊆ projectTorus '' torus := by
  intro x hx
  exact ⟨torusGraph x, torusGraph_mem hx, projectTorus_torusGraph x⟩
end Eden
