-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_33
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:55.58046+00:00
-- url     : https://prove2.me/submissions/5590698c-fd74-4190-9f30-236db4a383e4

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart33

set_option maxRecDepth 100000

/-- Chunk 348: 3 leaves. -/
theorem gt_chunk348_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_348
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 349: 2 leaves. -/
theorem gt_chunk349_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_349
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 350: 4 leaves. -/
theorem gt_chunk350_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_350
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 351: 4 leaves. -/
theorem gt_chunk351_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_351
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 352: 4 leaves. -/
theorem gt_chunk352_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_352
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 353: 3 leaves. -/
theorem gt_chunk353_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_353
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 354: 1 leaves. -/
theorem gt_chunk354_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_354
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true := by
  decide +kernel

/-- Chunk 355: 1 leaves. -/
theorem gt_chunk355_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_355
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) = true := by
  decide +kernel

/-- Chunk 356: 2 leaves. -/
theorem gt_chunk356_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_356
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 357: 2 leaves. -/
theorem gt_chunk357_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_357
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 358: 3 leaves. -/
theorem gt_chunk358_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_358
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 359: 2 leaves. -/
theorem gt_chunk359_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_359
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart33

open BirkhoffGlobalSection.TangentialHessian.GatePart33 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_348 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_349 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_350 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_351 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_352 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_353 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_354 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_355 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_356 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_357 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_358 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_359 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) :=
  ⟨gt_chunk348_ok, gt_chunk349_ok, gt_chunk350_ok, gt_chunk351_ok, gt_chunk352_ok, gt_chunk353_ok, gt_chunk354_ok, gt_chunk355_ok, gt_chunk356_ok, gt_chunk357_ok, gt_chunk358_ok, gt_chunk359_ok⟩
