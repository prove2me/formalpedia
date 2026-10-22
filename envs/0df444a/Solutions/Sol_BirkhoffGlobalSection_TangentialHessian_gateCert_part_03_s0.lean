-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_03_s0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:27.835008+00:00
-- url     : https://prove2.me/submissions/eb5d9626-8c3b-4b56-996a-55b924318210

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart03S0

set_option maxRecDepth 100000

/-- Chunk 33: 4 leaves. -/
theorem gt_chunk33_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_33
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 34: 2 leaves. -/
theorem gt_chunk34_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_34
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 35: 3 leaves. -/
theorem gt_chunk35_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_35
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 36: 4 leaves. -/
theorem gt_chunk36_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_36
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart03S0

open BirkhoffGlobalSection.TangentialHessian.GatePart03S0 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_33 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_34 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_35 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_36 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) :=
  ⟨gt_chunk33_ok, gt_chunk34_ok, gt_chunk35_ok, gt_chunk36_ok⟩
