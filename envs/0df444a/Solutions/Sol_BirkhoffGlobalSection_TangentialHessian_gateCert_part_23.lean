-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_23
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:43:56.253988+00:00
-- url     : https://prove2.me/submissions/8502c6ca-c676-4a07-9265-3d8e3b7bc455

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart23

set_option maxRecDepth 100000

/-- Chunk 232: 3 leaves. -/
theorem gt_chunk232_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_232
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 233: 1 leaves. -/
theorem gt_chunk233_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_233
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 234: 1 leaves. -/
theorem gt_chunk234_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_234
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 235: 2 leaves. -/
theorem gt_chunk235_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_235
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 236: 1 leaves. -/
theorem gt_chunk236_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_236
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 237: 1 leaves. -/
theorem gt_chunk237_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_237
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 238: 2 leaves. -/
theorem gt_chunk238_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_238
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 239: 1 leaves. -/
theorem gt_chunk239_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_239
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 240: 2 leaves. -/
theorem gt_chunk240_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_240
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 241: 1 leaves. -/
theorem gt_chunk241_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_241
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 242: 2 leaves. -/
theorem gt_chunk242_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_242
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart23

open BirkhoffGlobalSection.TangentialHessian.GatePart23 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_232 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_233 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_234 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_235 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_236 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_237 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_238 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_239 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_240 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_241 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_242 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true) :=
  ⟨gt_chunk232_ok, gt_chunk233_ok, gt_chunk234_ok, gt_chunk235_ok, gt_chunk236_ok, gt_chunk237_ok, gt_chunk238_ok, gt_chunk239_ok, gt_chunk240_ok, gt_chunk241_ok, gt_chunk242_ok⟩
