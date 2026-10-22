-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_13
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:24:02.909994+00:00
-- url     : https://prove2.me/submissions/60b8d785-5da8-489d-9fa9-91dcd6d7bbd5

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart13

set_option maxRecDepth 100000

/-- Chunk 132: 2 leaves. -/
theorem gt_chunk132_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_132
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 133: 2 leaves. -/
theorem gt_chunk133_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_133
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 134: 2 leaves. -/
theorem gt_chunk134_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_134
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 135: 1 leaves. -/
theorem gt_chunk135_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_135
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 136: 2 leaves. -/
theorem gt_chunk136_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_136
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 137: 2 leaves. -/
theorem gt_chunk137_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_137
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 138: 2 leaves. -/
theorem gt_chunk138_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_138
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 139: 2 leaves. -/
theorem gt_chunk139_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_139
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 140: 2 leaves. -/
theorem gt_chunk140_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_140
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart13

open BirkhoffGlobalSection.TangentialHessian.GatePart13 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_132 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_133 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_134 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_135 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_136 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_137 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_138 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_139 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_140 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) :=
  ⟨gt_chunk132_ok, gt_chunk133_ok, gt_chunk134_ok, gt_chunk135_ok, gt_chunk136_ok, gt_chunk137_ok, gt_chunk138_ok, gt_chunk139_ok, gt_chunk140_ok⟩
