-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_27
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:49.590986+00:00
-- url     : https://prove2.me/submissions/79a39215-7f05-491b-bdca-06b319348413

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart27

set_option maxRecDepth 100000

/-- Chunk 285: 2 leaves. -/
theorem gt_chunk285_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_285
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 286: 1 leaves. -/
theorem gt_chunk286_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_286
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 287: 1 leaves. -/
theorem gt_chunk287_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_287
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 288: 1 leaves. -/
theorem gt_chunk288_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_288
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 289: 3 leaves. -/
theorem gt_chunk289_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_289
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 290: 3 leaves. -/
theorem gt_chunk290_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_290
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 291: 3 leaves. -/
theorem gt_chunk291_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_291
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 292: 5 leaves. -/
theorem gt_chunk292_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_292
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 293: 1 leaves. -/
theorem gt_chunk293_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_293
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 294: 1 leaves. -/
theorem gt_chunk294_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_294
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 295: 2 leaves. -/
theorem gt_chunk295_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_295
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart27

open BirkhoffGlobalSection.TangentialHessian.GatePart27 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_285 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_286 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_287 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_288 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_289 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_290 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_291 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_292 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_293 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_294 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_295 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true) :=
  ⟨gt_chunk285_ok, gt_chunk286_ok, gt_chunk287_ok, gt_chunk288_ok, gt_chunk289_ok, gt_chunk290_ok, gt_chunk291_ok, gt_chunk292_ok, gt_chunk293_ok, gt_chunk294_ok, gt_chunk295_ok⟩
