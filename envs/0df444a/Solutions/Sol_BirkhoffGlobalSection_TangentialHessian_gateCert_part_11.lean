-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_11
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:24:00.837989+00:00
-- url     : https://prove2.me/submissions/3f51082a-8b45-4d66-8877-f3028203e286

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart11

set_option maxRecDepth 100000

/-- Chunk 113: 2 leaves. -/
theorem gt_chunk113_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_113
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 114: 2 leaves. -/
theorem gt_chunk114_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_114
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 115: 1 leaves. -/
theorem gt_chunk115_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_115
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 116: 2 leaves. -/
theorem gt_chunk116_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_116
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 117: 3 leaves. -/
theorem gt_chunk117_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_117
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 118: 3 leaves. -/
theorem gt_chunk118_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_118
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 119: 2 leaves. -/
theorem gt_chunk119_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_119
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 120: 2 leaves. -/
theorem gt_chunk120_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_120
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 121: 3 leaves. -/
theorem gt_chunk121_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_121
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart11

open BirkhoffGlobalSection.TangentialHessian.GatePart11 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_113 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_114 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_115 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_116 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_117 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_118 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_119 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_120 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_121 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) = true) :=
  ⟨gt_chunk113_ok, gt_chunk114_ok, gt_chunk115_ok, gt_chunk116_ok, gt_chunk117_ok, gt_chunk118_ok, gt_chunk119_ok, gt_chunk120_ok, gt_chunk121_ok⟩
