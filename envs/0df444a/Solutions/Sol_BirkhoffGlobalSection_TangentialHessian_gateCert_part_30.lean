-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_30
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:52.840985+00:00
-- url     : https://prove2.me/submissions/b40f0a5a-c147-4344-bdcf-02134a717348

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart30

set_option maxRecDepth 100000

/-- Chunk 314: 2 leaves. -/
theorem gt_chunk314_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_314
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 315: 3 leaves. -/
theorem gt_chunk315_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_315
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 316: 2 leaves. -/
theorem gt_chunk316_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_316
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 317: 1 leaves. -/
theorem gt_chunk317_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_317
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 318: 2 leaves. -/
theorem gt_chunk318_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_318
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 319: 2 leaves. -/
theorem gt_chunk319_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_319
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 320: 3 leaves. -/
theorem gt_chunk320_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_320
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 321: 5 leaves. -/
theorem gt_chunk321_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_321
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 322: 1 leaves. -/
theorem gt_chunk322_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_322
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart30

open BirkhoffGlobalSection.TangentialHessian.GatePart30 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_314 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_315 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_316 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_317 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_318 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_319 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_320 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_321 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_322 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 2) = true) :=
  ⟨gt_chunk314_ok, gt_chunk315_ok, gt_chunk316_ok, gt_chunk317_ok, gt_chunk318_ok, gt_chunk319_ok, gt_chunk320_ok, gt_chunk321_ok, gt_chunk322_ok⟩
