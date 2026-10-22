-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_05_s1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:33.473602+00:00
-- url     : https://prove2.me/submissions/b2754e6d-36fd-4ad3-afb8-ac58ec837957

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart05S1

set_option maxRecDepth 100000

/-- Chunk 61: 5 leaves. -/
theorem gt_chunk61_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_61
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) = true := by
  decide +kernel

/-- Chunk 62: 3 leaves. -/
theorem gt_chunk62_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_62
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 63: 2 leaves. -/
theorem gt_chunk63_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_63
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 64: 2 leaves. -/
theorem gt_chunk64_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_64
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 65: 2 leaves. -/
theorem gt_chunk65_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_65
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart05S1

open BirkhoffGlobalSection.TangentialHessian.GatePart05S1 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_61 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_62 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_63 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_64 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_65 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true) :=
  ⟨gt_chunk61_ok, gt_chunk62_ok, gt_chunk63_ok, gt_chunk64_ok, gt_chunk65_ok⟩
