-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_34
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:56.431522+00:00
-- url     : https://prove2.me/submissions/62be061b-c977-4660-b497-4fe202e4dc80

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart34

set_option maxRecDepth 100000

/-- Chunk 360: 2 leaves. -/
theorem gt_chunk360_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_360
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 361: 2 leaves. -/
theorem gt_chunk361_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_361
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 362: 4 leaves. -/
theorem gt_chunk362_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_362
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true := by
  decide +kernel

/-- Chunk 363: 3 leaves. -/
theorem gt_chunk363_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_363
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) = true := by
  decide +kernel

/-- Chunk 364: 9 leaves. -/
theorem gt_chunk364_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_364
      (upperHalf (upperHalf (upperHalf rootBox 0) 1) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart34

open BirkhoffGlobalSection.TangentialHessian.GatePart34 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_360 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_361 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_362 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_363 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_364 (upperHalf (upperHalf (upperHalf rootBox 0) 1) 1) = true) :=
  ⟨gt_chunk360_ok, gt_chunk361_ok, gt_chunk362_ok, gt_chunk363_ok, gt_chunk364_ok⟩
