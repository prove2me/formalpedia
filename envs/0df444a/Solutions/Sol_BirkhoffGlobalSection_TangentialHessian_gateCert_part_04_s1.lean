-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_04_s1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:31.314385+00:00
-- url     : https://prove2.me/submissions/d0a6c1dd-0064-4cd2-87e8-dc467d0b6e54

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart04S1

set_option maxRecDepth 100000

/-- Chunk 50: 2 leaves. -/
theorem gt_chunk50_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_50
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 51: 4 leaves. -/
theorem gt_chunk51_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_51
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 52: 2 leaves. -/
theorem gt_chunk52_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_52
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 53: 2 leaves. -/
theorem gt_chunk53_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_53
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 54: 2 leaves. -/
theorem gt_chunk54_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_54
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 55: 2 leaves. -/
theorem gt_chunk55_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_55
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart04S1

open BirkhoffGlobalSection.TangentialHessian.GatePart04S1 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_50 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_51 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_52 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_53 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_54 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_55 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) :=
  ⟨gt_chunk50_ok, gt_chunk51_ok, gt_chunk52_ok, gt_chunk53_ok, gt_chunk54_ok, gt_chunk55_ok⟩
