-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_05_s0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:32.179324+00:00
-- url     : https://prove2.me/submissions/cec0a11d-dbcc-4c23-944e-8f96427af7c3

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart05S0

set_option maxRecDepth 100000

/-- Chunk 56: 3 leaves. -/
theorem gt_chunk56_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_56
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 57: 4 leaves. -/
theorem gt_chunk57_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_57
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 58: 3 leaves. -/
theorem gt_chunk58_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_58
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 59: 4 leaves. -/
theorem gt_chunk59_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_59
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 60: 3 leaves. -/
theorem gt_chunk60_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_60
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart05S0

open BirkhoffGlobalSection.TangentialHessian.GatePart05S0 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_56 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_57 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_58 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_59 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_60 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) :=
  ⟨gt_chunk56_ok, gt_chunk57_ok, gt_chunk58_ok, gt_chunk59_ok, gt_chunk60_ok⟩
