-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_12
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T18:27:42.721104+00:00
-- url     : https://prove2.me/submissions/3cd8eafb-47bb-42cf-903c-6ea9c009a63e

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart12

set_option maxRecDepth 100000

/-- Chunk 122: 3 leaves. -/
theorem gt_chunk122_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_122
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 123: 1 leaves. -/
theorem gt_chunk123_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_123
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 124: 2 leaves. -/
theorem gt_chunk124_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_124
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 125: 2 leaves. -/
theorem gt_chunk125_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_125
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 126: 2 leaves. -/
theorem gt_chunk126_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_126
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 127: 2 leaves. -/
theorem gt_chunk127_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_127
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 128: 1 leaves. -/
theorem gt_chunk128_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_128
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 129: 2 leaves. -/
theorem gt_chunk129_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_129
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 130: 2 leaves. -/
theorem gt_chunk130_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_130
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 131: 2 leaves. -/
theorem gt_chunk131_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_131
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart12

open BirkhoffGlobalSection.TangentialHessian.GatePart12 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_122 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_123 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_124 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_125 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_126 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_127 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_128 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_129 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_130 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_131 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) :=
  ⟨gt_chunk122_ok, gt_chunk123_ok, gt_chunk124_ok, gt_chunk125_ok, gt_chunk126_ok, gt_chunk127_ok, gt_chunk128_ok, gt_chunk129_ok, gt_chunk130_ok, gt_chunk131_ok⟩
