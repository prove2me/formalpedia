-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:29.469721+00:00
-- url     : https://prove2.me/submissions/72f156b9-9451-49ae-a3bb-5544f7f9a70a

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart01S1

set_option maxRecDepth 100000

/-- Chunk 14: 4 leaves. -/
theorem gt_chunk14_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_14
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 15: 2 leaves. -/
theorem gt_chunk15_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_15
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 16: 3 leaves. -/
theorem gt_chunk16_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_16
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 17: 4 leaves. -/
theorem gt_chunk17_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_17
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart01S1

open BirkhoffGlobalSection.TangentialHessian.GatePart01S1 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_14 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_15 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_16 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_17 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) :=
  ⟨gt_chunk14_ok, gt_chunk15_ok, gt_chunk16_ok, gt_chunk17_ok⟩
