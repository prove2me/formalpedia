-- Prove2me | solution 1 for Eden.range_torusParametrization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:47.941432+00:00
-- url     : https://prove2.me/submissions/8b345f40-ed09-4cc0-8e1a-fde0caa14422

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
import Theorems.Thm_Eden_exists_torusPoint_of_mem
import Theorems.Thm_Eden_torusPoint_mem


set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden
namespace Eden
theorem _root_.solution : range torusParametrization = torus := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact torusPoint_mem _ _
  · intro hp
    obtain ⟨a, b, hab⟩ := exists_torusPoint_of_mem hp
    exact ⟨!₂[a, b], hab⟩
end Eden
