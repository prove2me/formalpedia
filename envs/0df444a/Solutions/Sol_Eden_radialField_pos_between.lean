-- Prove2me | solution 1 for Eden.radialField_pos_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:29.634342+00:00
-- url     : https://prove2.me/submissions/5f59a12e-e868-45e7-b03f-0f5b5ab1ab6e

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {r : ℝ} (hr₁ : 1 < r) (hr₂ : r < Real.sqrt 2) :
    radialField r > 0 := by
  have h₁ : 0 < r ^ 2 - 1 := by nlinarith
  have h₂ : r ^ 2 - 2 < 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) h₁) h₂
end Eden
