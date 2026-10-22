-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_01
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:55:21.092825+00:00
-- url     : https://prove2.me/submissions/4a315dd4-ac25-446f-b567-50386cf207ad

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01_s0
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01_s1
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01_s2
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

/-- Part 1: the conjunction of its 3 sub-parts. -/
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_10 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_11 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_12 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_13 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_14 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_15 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_16 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_17 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_18 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_19 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_20 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) := by
  obtain ⟨h0, h1, h2, h3⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s0
  obtain ⟨h4, h5, h6, h7⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s1
  obtain ⟨h8, h9, h10⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s2
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
