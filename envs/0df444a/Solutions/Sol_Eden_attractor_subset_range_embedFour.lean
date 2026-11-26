-- Prove2me | solution 1 for Eden.attractor_subset_range_embedFour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:47.302037+00:00
-- url     : https://prove2.me/submissions/c9f5369a-a3ea-43ad-b28d-82b3c7898a90

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
import Theorems.Thm_Eden_embedFour_projectFour

set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden
namespace Eden
theorem _root_.solution : attractor ⊆ range embedFour := by
  intro p hp
  exact ⟨projectFour p, embedFour_projectFour hp.2.2⟩
end Eden
