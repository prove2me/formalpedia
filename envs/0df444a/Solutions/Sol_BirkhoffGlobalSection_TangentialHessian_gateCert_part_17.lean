-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_17
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:43:50.33531+00:00
-- url     : https://prove2.me/submissions/368dce82-9961-4dcc-9245-e83412a937a1

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart17

set_option maxRecDepth 100000

/-- Chunk 171: 2 leaves. -/
theorem gt_chunk171_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_171
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 172: 2 leaves. -/
theorem gt_chunk172_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_172
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 173: 5 leaves. -/
theorem gt_chunk173_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_173
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 174: 2 leaves. -/
theorem gt_chunk174_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_174
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 175: 3 leaves. -/
theorem gt_chunk175_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_175
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 176: 3 leaves. -/
theorem gt_chunk176_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_176
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 177: 1 leaves. -/
theorem gt_chunk177_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_177
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 178: 1 leaves. -/
theorem gt_chunk178_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_178
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 179: 2 leaves. -/
theorem gt_chunk179_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_179
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 180: 2 leaves. -/
theorem gt_chunk180_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_180
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart17

open BirkhoffGlobalSection.TangentialHessian.GatePart17 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_171 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_172 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_173 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_174 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_175 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_176 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_177 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_178 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_179 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_180 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) = true) :=
  ⟨gt_chunk171_ok, gt_chunk172_ok, gt_chunk173_ok, gt_chunk174_ok, gt_chunk175_ok, gt_chunk176_ok, gt_chunk177_ok, gt_chunk178_ok, gt_chunk179_ok, gt_chunk180_ok⟩
