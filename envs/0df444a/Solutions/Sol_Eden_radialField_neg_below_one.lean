-- Prove2me | solution 1 for Eden.radialField_neg_below_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:28.778311+00:00
-- url     : https://prove2.me/submissions/631c6c33-bea3-40be-8745-123ef5b2a6d0

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    radialField r < 0 := by
  have h₁ : r ^ 2 - 1 < 0 := by nlinarith
  have h₂ : r ^ 2 - 2 < 0 := by nlinarith
  exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (neg_neg_of_pos hr) h₁) h₂
end Eden
