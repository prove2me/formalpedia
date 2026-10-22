-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_04_s0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:30.506395+00:00
-- url     : https://prove2.me/submissions/00f992f5-f74b-4116-ad55-8fd86c01966b

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart04S0

set_option maxRecDepth 100000

/-- Chunk 44: 2 leaves. -/
theorem gt_chunk44_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_44
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 45: 2 leaves. -/
theorem gt_chunk45_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_45
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 46: 3 leaves. -/
theorem gt_chunk46_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_46
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 47: 2 leaves. -/
theorem gt_chunk47_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_47
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 48: 2 leaves. -/
theorem gt_chunk48_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_48
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 49: 2 leaves. -/
theorem gt_chunk49_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_49
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart04S0

open BirkhoffGlobalSection.TangentialHessian.GatePart04S0 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_44 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_45 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_46 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_47 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_48 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_49 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) :=
  ⟨gt_chunk44_ok, gt_chunk45_ok, gt_chunk46_ok, gt_chunk47_ok, gt_chunk48_ok, gt_chunk49_ok⟩
