-- Prove2me | solution 1 for Eden.torusEvolution_no_positive_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:16:55.162639+00:00
-- url     : https://prove2.me/submissions/50c7cbf3-18b7-43aa-9558-cd21177f5ea5

import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_Uniqueness
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Eden_TorusRecurrence
import Theorems.Thm_Eden_torus_no_positive_return


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : torus) {t : ℝ} (ht : 0 < t) :
    torusEvolution c t p ≠ p := by
  intro h
  exact torus_no_positive_return c p.property ht (congrArg Subtype.val h)
end Eden
