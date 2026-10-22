-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_24
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:43:57.068076+00:00
-- url     : https://prove2.me/submissions/0b96a695-87ce-456f-85a5-1055655b82a4

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart24

set_option maxRecDepth 100000

/-- Chunk 243: 2 leaves. -/
theorem gt_chunk243_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_243
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 244: 2 leaves. -/
theorem gt_chunk244_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_244
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 245: 2 leaves. -/
theorem gt_chunk245_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_245
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 246: 1 leaves. -/
theorem gt_chunk246_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_246
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) 1) 0) = true := by
  decide +kernel

/-- Chunk 247: 1 leaves. -/
theorem gt_chunk247_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_247
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) 1) 0) = true := by
  decide +kernel

/-- Chunk 248: 1 leaves. -/
theorem gt_chunk248_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_248
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 249: 2 leaves. -/
theorem gt_chunk249_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_249
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 250: 2 leaves. -/
theorem gt_chunk250_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_250
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 251: 1 leaves. -/
theorem gt_chunk251_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_251
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 252: 1 leaves. -/
theorem gt_chunk252_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_252
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 253: 1 leaves. -/
theorem gt_chunk253_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_253
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 254: 2 leaves. -/
theorem gt_chunk254_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_254
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart24

open BirkhoffGlobalSection.TangentialHessian.GatePart24 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_243 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_244 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_245 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_246 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_247 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_248 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_249 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_250 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_251 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_252 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_253 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_254 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true) :=
  ⟨gt_chunk243_ok, gt_chunk244_ok, gt_chunk245_ok, gt_chunk246_ok, gt_chunk247_ok, gt_chunk248_ok, gt_chunk249_ok, gt_chunk250_ok, gt_chunk251_ok, gt_chunk252_ok, gt_chunk253_ok, gt_chunk254_ok⟩
