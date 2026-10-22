-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_14
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:24:03.92134+00:00
-- url     : https://prove2.me/submissions/f3ff2f43-2357-45bf-941f-6bc3346fc263

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart14

set_option maxRecDepth 100000

/-- Chunk 141: 1 leaves. -/
theorem gt_chunk141_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_141
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 142: 2 leaves. -/
theorem gt_chunk142_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_142
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 143: 2 leaves. -/
theorem gt_chunk143_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_143
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 144: 2 leaves. -/
theorem gt_chunk144_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_144
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 145: 1 leaves. -/
theorem gt_chunk145_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_145
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 146: 1 leaves. -/
theorem gt_chunk146_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_146
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 147: 2 leaves. -/
theorem gt_chunk147_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_147
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 148: 2 leaves. -/
theorem gt_chunk148_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_148
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 149: 2 leaves. -/
theorem gt_chunk149_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_149
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 150: 1 leaves. -/
theorem gt_chunk150_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_150
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart14

open BirkhoffGlobalSection.TangentialHessian.GatePart14 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_141 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_142 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_143 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_144 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_145 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_146 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_147 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_148 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_149 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_150 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 2) 0) 1) = true) :=
  ⟨gt_chunk141_ok, gt_chunk142_ok, gt_chunk143_ok, gt_chunk144_ok, gt_chunk145_ok, gt_chunk146_ok, gt_chunk147_ok, gt_chunk148_ok, gt_chunk149_ok, gt_chunk150_ok⟩
