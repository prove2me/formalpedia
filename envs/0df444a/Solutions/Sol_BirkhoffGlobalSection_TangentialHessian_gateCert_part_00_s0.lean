-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_00_s0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:25.46066+00:00
-- url     : https://prove2.me/submissions/27576fff-dd42-468e-824d-ce1d79f07bf5

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart00S0

set_option maxRecDepth 100000

/-- Chunk 0: 5 leaves. -/
theorem gt_chunk0_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_0
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 1: 4 leaves. -/
theorem gt_chunk1_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_1
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 2: 2 leaves. -/
theorem gt_chunk2_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_2
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 3: 3 leaves. -/
theorem gt_chunk3_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_3
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart00S0

open BirkhoffGlobalSection.TangentialHessian.GatePart00S0 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_0 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_1 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_2 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_3 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 2) 2) 1) = true) :=
  ⟨gt_chunk0_ok, gt_chunk1_ok, gt_chunk2_ok, gt_chunk3_ok⟩
