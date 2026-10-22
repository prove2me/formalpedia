-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_03
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:55:23.88912+00:00
-- url     : https://prove2.me/submissions/7e0938b3-7438-44be-95b0-15601d08c671

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_03_s0
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_03_s1
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_03_s2
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

/-- Part 3: the conjunction of its 3 sub-parts. -/
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_33 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_34 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_35 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_36 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_37 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_38 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_39 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_40 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_41 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_42 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_43 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) := by
  obtain ⟨h0, h1, h2, h3⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_03_s0
  obtain ⟨h4, h5, h6, h7, h8⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_03_s1
  obtain ⟨h9, h10⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_03_s2
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
