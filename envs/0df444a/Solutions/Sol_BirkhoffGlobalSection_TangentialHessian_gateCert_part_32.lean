-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_32
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:54.68851+00:00
-- url     : https://prove2.me/submissions/b79b65a8-27eb-4116-b116-4f2ef3b6a220

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart32

set_option maxRecDepth 100000

/-- Chunk 336: 2 leaves. -/
theorem gt_chunk336_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_336
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 337: 2 leaves. -/
theorem gt_chunk337_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_337
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 338: 2 leaves. -/
theorem gt_chunk338_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_338
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 339: 1 leaves. -/
theorem gt_chunk339_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_339
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 340: 2 leaves. -/
theorem gt_chunk340_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_340
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 341: 3 leaves. -/
theorem gt_chunk341_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_341
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 342: 4 leaves. -/
theorem gt_chunk342_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_342
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 343: 6 leaves. -/
theorem gt_chunk343_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_343
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) = true := by
  decide +kernel

/-- Chunk 344: 3 leaves. -/
theorem gt_chunk344_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_344
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true := by
  decide +kernel

/-- Chunk 345: 2 leaves. -/
theorem gt_chunk345_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_345
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 346: 2 leaves. -/
theorem gt_chunk346_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_346
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 347: 2 leaves. -/
theorem gt_chunk347_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_347
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart32

open BirkhoffGlobalSection.TangentialHessian.GatePart32 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_336 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_337 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_338 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_339 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_340 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_341 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_342 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_343 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_344 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_345 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_346 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_347 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 2) 1) = true) :=
  ⟨gt_chunk336_ok, gt_chunk337_ok, gt_chunk338_ok, gt_chunk339_ok, gt_chunk340_ok, gt_chunk341_ok, gt_chunk342_ok, gt_chunk343_ok, gt_chunk344_ok, gt_chunk345_ok, gt_chunk346_ok, gt_chunk347_ok⟩
