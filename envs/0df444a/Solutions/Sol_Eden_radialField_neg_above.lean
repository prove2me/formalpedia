-- Prove2me | solution 1 for Eden.radialField_neg_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:32.680864+00:00
-- url     : https://prove2.me/submissions/8c303899-a5e3-4c8a-9aab-9bb0fc90c397

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {r : ℝ} (hr : Real.sqrt 2 < r) :
    radialField r < 0 := by
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h₁ : 0 < r ^ 2 - 1 := by nlinarith
  have h₂ : 0 < r ^ 2 - 2 := by nlinarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) h₁) h₂
end Eden
