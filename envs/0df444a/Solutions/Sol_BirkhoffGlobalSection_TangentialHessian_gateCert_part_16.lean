-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_16
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:43:49.240741+00:00
-- url     : https://prove2.me/submissions/78122d19-2d1f-4406-a1f6-14ac426990b4

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart16

set_option maxRecDepth 100000

/-- Chunk 160: 2 leaves. -/
theorem gt_chunk160_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_160
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 161: 2 leaves. -/
theorem gt_chunk161_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_161
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) = true := by
  decide +kernel

/-- Chunk 162: 1 leaves. -/
theorem gt_chunk162_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_162
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 163: 1 leaves. -/
theorem gt_chunk163_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_163
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 164: 1 leaves. -/
theorem gt_chunk164_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_164
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 165: 1 leaves. -/
theorem gt_chunk165_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_165
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 166: 1 leaves. -/
theorem gt_chunk166_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_166
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) = true := by
  decide +kernel

/-- Chunk 167: 1 leaves. -/
theorem gt_chunk167_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_167
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 168: 1 leaves. -/
theorem gt_chunk168_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_168
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 169: 2 leaves. -/
theorem gt_chunk169_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_169
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 170: 2 leaves. -/
theorem gt_chunk170_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_170
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart16

open BirkhoffGlobalSection.TangentialHessian.GatePart16 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_160 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_161 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_162 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_163 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_164 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_165 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_166 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_167 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_168 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_169 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_170 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 0) 2) = true) :=
  ⟨gt_chunk160_ok, gt_chunk161_ok, gt_chunk162_ok, gt_chunk163_ok, gt_chunk164_ok, gt_chunk165_ok, gt_chunk166_ok, gt_chunk167_ok, gt_chunk168_ok, gt_chunk169_ok, gt_chunk170_ok⟩
