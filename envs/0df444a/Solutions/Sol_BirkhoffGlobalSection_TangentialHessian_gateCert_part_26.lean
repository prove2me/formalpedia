-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_26
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:48.684752+00:00
-- url     : https://prove2.me/submissions/9c5dc9f5-8289-4c8a-8d17-54d12ca0262a

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart26

set_option maxRecDepth 100000

/-- Chunk 268: 1 leaves. -/
theorem gt_chunk268_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_268
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 269: 1 leaves. -/
theorem gt_chunk269_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_269
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 270: 1 leaves. -/
theorem gt_chunk270_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_270
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 271: 3 leaves. -/
theorem gt_chunk271_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_271
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 272: 2 leaves. -/
theorem gt_chunk272_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_272
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 273: 2 leaves. -/
theorem gt_chunk273_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_273
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 274: 1 leaves. -/
theorem gt_chunk274_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_274
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 275: 1 leaves. -/
theorem gt_chunk275_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_275
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 276: 1 leaves. -/
theorem gt_chunk276_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_276
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 277: 3 leaves. -/
theorem gt_chunk277_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_277
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 278: 3 leaves. -/
theorem gt_chunk278_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_278
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 279: 1 leaves. -/
theorem gt_chunk279_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_279
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 280: 1 leaves. -/
theorem gt_chunk280_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_280
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) = true := by
  decide +kernel

/-- Chunk 281: 1 leaves. -/
theorem gt_chunk281_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_281
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) = true := by
  decide +kernel

/-- Chunk 282: 1 leaves. -/
theorem gt_chunk282_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_282
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 283: 2 leaves. -/
theorem gt_chunk283_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_283
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 284: 1 leaves. -/
theorem gt_chunk284_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_284
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart26

open BirkhoffGlobalSection.TangentialHessian.GatePart26 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_268 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_269 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_270 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_271 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_272 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_273 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_274 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_275 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_276 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_277 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_278 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_279 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_280 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_281 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_282 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_283 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_284 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true) :=
  ⟨gt_chunk268_ok, gt_chunk269_ok, gt_chunk270_ok, gt_chunk271_ok, gt_chunk272_ok, gt_chunk273_ok, gt_chunk274_ok, gt_chunk275_ok, gt_chunk276_ok, gt_chunk277_ok, gt_chunk278_ok, gt_chunk279_ok, gt_chunk280_ok, gt_chunk281_ok, gt_chunk282_ok, gt_chunk283_ok, gt_chunk284_ok⟩
