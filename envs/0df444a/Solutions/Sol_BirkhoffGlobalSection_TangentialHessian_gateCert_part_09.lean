-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_09
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:23:58.678986+00:00
-- url     : https://prove2.me/submissions/d0781a3e-4f22-47cb-a97c-bf9fe9ebb867

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart09

set_option maxRecDepth 100000

/-- Chunk 94: 2 leaves. -/
theorem gt_chunk94_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_94
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 95: 1 leaves. -/
theorem gt_chunk95_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_95
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 96: 2 leaves. -/
theorem gt_chunk96_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_96
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 97: 2 leaves. -/
theorem gt_chunk97_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_97
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 98: 2 leaves. -/
theorem gt_chunk98_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_98
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 99: 3 leaves. -/
theorem gt_chunk99_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_99
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 100: 2 leaves. -/
theorem gt_chunk100_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_100
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 101: 2 leaves. -/
theorem gt_chunk101_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_101
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 102: 1 leaves. -/
theorem gt_chunk102_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_102
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 103: 3 leaves. -/
theorem gt_chunk103_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_103
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart09

open BirkhoffGlobalSection.TangentialHessian.GatePart09 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_94 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_95 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_96 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_97 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_98 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_99 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_100 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_101 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_102 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_103 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) :=
  ⟨gt_chunk94_ok, gt_chunk95_ok, gt_chunk96_ok, gt_chunk97_ok, gt_chunk98_ok, gt_chunk99_ok, gt_chunk100_ok, gt_chunk101_ok, gt_chunk102_ok, gt_chunk103_ok⟩
