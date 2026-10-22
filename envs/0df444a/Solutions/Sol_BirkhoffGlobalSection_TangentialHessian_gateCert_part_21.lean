-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_21
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:43:54.188979+00:00
-- url     : https://prove2.me/submissions/90d50bca-87c1-46e6-a596-36df6ab56489

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart21

set_option maxRecDepth 100000

/-- Chunk 214: 2 leaves. -/
theorem gt_chunk214_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_214
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 215: 2 leaves. -/
theorem gt_chunk215_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_215
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 216: 2 leaves. -/
theorem gt_chunk216_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_216
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 217: 1 leaves. -/
theorem gt_chunk217_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_217
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 218: 1 leaves. -/
theorem gt_chunk218_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_218
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 219: 1 leaves. -/
theorem gt_chunk219_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_219
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 220: 1 leaves. -/
theorem gt_chunk220_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_220
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 221: 1 leaves. -/
theorem gt_chunk221_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_221
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 222: 1 leaves. -/
theorem gt_chunk222_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_222
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 223: 2 leaves. -/
theorem gt_chunk223_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_223
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart21

open BirkhoffGlobalSection.TangentialHessian.GatePart21 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_214 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_215 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_216 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_217 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_218 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_219 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_220 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_221 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_222 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_223 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) = true) :=
  ⟨gt_chunk214_ok, gt_chunk215_ok, gt_chunk216_ok, gt_chunk217_ok, gt_chunk218_ok, gt_chunk219_ok, gt_chunk220_ok, gt_chunk221_ok, gt_chunk222_ok, gt_chunk223_ok⟩
