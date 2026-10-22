-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_28
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:50.978614+00:00
-- url     : https://prove2.me/submissions/7c45c046-1d67-41c2-9087-de5266e6883d

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart28

set_option maxRecDepth 100000

/-- Chunk 296: 2 leaves. -/
theorem gt_chunk296_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_296
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 297: 1 leaves. -/
theorem gt_chunk297_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_297
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 298: 2 leaves. -/
theorem gt_chunk298_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_298
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 299: 2 leaves. -/
theorem gt_chunk299_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_299
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 300: 2 leaves. -/
theorem gt_chunk300_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_300
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 301: 4 leaves. -/
theorem gt_chunk301_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_301
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 302: 2 leaves. -/
theorem gt_chunk302_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_302
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 303: 1 leaves. -/
theorem gt_chunk303_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_303
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart28

open BirkhoffGlobalSection.TangentialHessian.GatePart28 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_296 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_297 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_298 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_299 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_300 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_301 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_302 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_303 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) :=
  ⟨gt_chunk296_ok, gt_chunk297_ok, gt_chunk298_ok, gt_chunk299_ok, gt_chunk300_ok, gt_chunk301_ok, gt_chunk302_ok, gt_chunk303_ok⟩
