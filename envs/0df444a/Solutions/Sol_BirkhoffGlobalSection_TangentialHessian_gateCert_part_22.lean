-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_22
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:43:55.279458+00:00
-- url     : https://prove2.me/submissions/4814484d-2517-4b03-896f-436f65f34566

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart22

set_option maxRecDepth 100000

/-- Chunk 224: 2 leaves. -/
theorem gt_chunk224_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_224
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 225: 2 leaves. -/
theorem gt_chunk225_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_225
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 226: 2 leaves. -/
theorem gt_chunk226_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_226
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 227: 2 leaves. -/
theorem gt_chunk227_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_227
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 228: 1 leaves. -/
theorem gt_chunk228_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_228
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 229: 1 leaves. -/
theorem gt_chunk229_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_229
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 230: 1 leaves. -/
theorem gt_chunk230_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_230
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 231: 2 leaves. -/
theorem gt_chunk231_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_231
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart22

open BirkhoffGlobalSection.TangentialHessian.GatePart22 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_224 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_225 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_226 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_227 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_228 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_229 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_230 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_231 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true) :=
  ⟨gt_chunk224_ok, gt_chunk225_ok, gt_chunk226_ok, gt_chunk227_ok, gt_chunk228_ok, gt_chunk229_ok, gt_chunk230_ok, gt_chunk231_ok⟩
