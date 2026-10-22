-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_00
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:55:20.244743+00:00
-- url     : https://prove2.me/submissions/0198f42c-ab71-4993-84ba-9891c042af57

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_00_s0
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_00_s1
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_00_s2
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

/-- Part 0: the conjunction of its 3 sub-parts. -/
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_0 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_1 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_2 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_3 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_4 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_5 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_6 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_7 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_8 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_9 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true) := by
  obtain ⟨h0, h1, h2, h3⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_00_s0
  obtain ⟨h4, h5, h6, h7, h8⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_00_s1
  obtain h9 := BirkhoffGlobalSection.TangentialHessian.gateCert_part_00_s2
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
