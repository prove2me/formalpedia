-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_05
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:55:25.753061+00:00
-- url     : https://prove2.me/submissions/a873ca75-cc9a-4cb5-bccb-33665112b73a

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_05_s0
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_05_s1
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_05_s2
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

/-- Part 5: the conjunction of its 3 sub-parts. -/
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_56 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_57 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_58 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_59 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_60 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_61 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_62 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_63 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_64 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_65 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_66 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_05_s0
  obtain ⟨h5, h6, h7, h8, h9⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_05_s1
  obtain h10 := BirkhoffGlobalSection.TangentialHessian.gateCert_part_05_s2
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
