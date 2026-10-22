-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_02_s0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:31.039048+00:00
-- url     : https://prove2.me/submissions/9e409865-24f4-458e-89c9-1a3e4ccf3363

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart02S0

set_option maxRecDepth 100000

/-- Chunk 21: 2 leaves. -/
theorem gt_chunk21_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_21
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 22: 2 leaves. -/
theorem gt_chunk22_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_22
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 23: 2 leaves. -/
theorem gt_chunk23_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_23
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 24: 3 leaves. -/
theorem gt_chunk24_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_24
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 25: 2 leaves. -/
theorem gt_chunk25_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_25
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart02S0

open BirkhoffGlobalSection.TangentialHessian.GatePart02S0 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_21 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_22 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_23 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_24 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_25 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) :=
  ⟨gt_chunk21_ok, gt_chunk22_ok, gt_chunk23_ok, gt_chunk24_ok, gt_chunk25_ok⟩
