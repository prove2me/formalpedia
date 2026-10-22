-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_02_s1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:31.836522+00:00
-- url     : https://prove2.me/submissions/e606bb15-9775-47b0-ba7d-5ba87914f05d

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart02S1

set_option maxRecDepth 100000

/-- Chunk 26: 3 leaves. -/
theorem gt_chunk26_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_26
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 27: 2 leaves. -/
theorem gt_chunk27_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_27
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 28: 2 leaves. -/
theorem gt_chunk28_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_28
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 29: 2 leaves. -/
theorem gt_chunk29_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_29
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 30: 2 leaves. -/
theorem gt_chunk30_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_30
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart02S1

open BirkhoffGlobalSection.TangentialHessian.GatePart02S1 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_26 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_27 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_28 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_29 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_30 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true) :=
  ⟨gt_chunk26_ok, gt_chunk27_ok, gt_chunk28_ok, gt_chunk29_ok, gt_chunk30_ok⟩
