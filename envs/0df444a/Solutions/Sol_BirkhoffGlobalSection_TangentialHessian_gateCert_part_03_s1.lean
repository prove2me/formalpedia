-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_03_s1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:28.821242+00:00
-- url     : https://prove2.me/submissions/5a69ccbd-3ebc-4926-a0e2-c8c0a65ca2d9

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart03S1

set_option maxRecDepth 100000

/-- Chunk 37: 2 leaves. -/
theorem gt_chunk37_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_37
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 38: 2 leaves. -/
theorem gt_chunk38_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_38
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 39: 2 leaves. -/
theorem gt_chunk39_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_39
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 40: 4 leaves. -/
theorem gt_chunk40_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_40
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 41: 2 leaves. -/
theorem gt_chunk41_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_41
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart03S1

open BirkhoffGlobalSection.TangentialHessian.GatePart03S1 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_37 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_38 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_39 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_40 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_41 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) :=
  ⟨gt_chunk37_ok, gt_chunk38_ok, gt_chunk39_ok, gt_chunk40_ok, gt_chunk41_ok⟩
