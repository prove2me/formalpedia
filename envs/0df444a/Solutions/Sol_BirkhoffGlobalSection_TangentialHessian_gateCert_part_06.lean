-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_06
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:23:56.168985+00:00
-- url     : https://prove2.me/submissions/49acb1b7-ef0c-4cb9-ab2f-ad905af92b2a

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart06

set_option maxRecDepth 100000

/-- Chunk 67: 3 leaves. -/
theorem gt_chunk67_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_67
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 68: 2 leaves. -/
theorem gt_chunk68_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_68
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 69: 2 leaves. -/
theorem gt_chunk69_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_69
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 70: 2 leaves. -/
theorem gt_chunk70_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_70
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 71: 2 leaves. -/
theorem gt_chunk71_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_71
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 72: 2 leaves. -/
theorem gt_chunk72_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_72
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 73: 1 leaves. -/
theorem gt_chunk73_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_73
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 74: 2 leaves. -/
theorem gt_chunk74_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_74
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 75: 2 leaves. -/
theorem gt_chunk75_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_75
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart06

open BirkhoffGlobalSection.TangentialHessian.GatePart06 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_67 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_68 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_69 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_70 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_71 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_72 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_73 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_74 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_75 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 0) = true) :=
  ⟨gt_chunk67_ok, gt_chunk68_ok, gt_chunk69_ok, gt_chunk70_ok, gt_chunk71_ok, gt_chunk72_ok, gt_chunk73_ok, gt_chunk74_ok, gt_chunk75_ok⟩
