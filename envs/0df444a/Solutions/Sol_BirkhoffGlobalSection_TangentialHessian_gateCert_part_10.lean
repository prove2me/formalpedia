-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_10
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:23:59.509327+00:00
-- url     : https://prove2.me/submissions/7cac65de-ca64-4155-99ec-5dbf51a45368

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart10

set_option maxRecDepth 100000

/-- Chunk 104: 3 leaves. -/
theorem gt_chunk104_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_104
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 105: 2 leaves. -/
theorem gt_chunk105_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_105
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 106: 2 leaves. -/
theorem gt_chunk106_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_106
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 107: 2 leaves. -/
theorem gt_chunk107_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_107
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 108: 1 leaves. -/
theorem gt_chunk108_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_108
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 109: 2 leaves. -/
theorem gt_chunk109_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_109
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 110: 2 leaves. -/
theorem gt_chunk110_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_110
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 111: 1 leaves. -/
theorem gt_chunk111_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_111
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 112: 2 leaves. -/
theorem gt_chunk112_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_112
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart10

open BirkhoffGlobalSection.TangentialHessian.GatePart10 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_104 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_105 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_106 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_107 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_108 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_109 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_110 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_111 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_112 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) :=
  ⟨gt_chunk104_ok, gt_chunk105_ok, gt_chunk106_ok, gt_chunk107_ok, gt_chunk108_ok, gt_chunk109_ok, gt_chunk110_ok, gt_chunk111_ok, gt_chunk112_ok⟩
