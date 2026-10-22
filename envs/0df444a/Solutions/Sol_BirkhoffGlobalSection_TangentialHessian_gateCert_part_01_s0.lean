-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:28.061025+00:00
-- url     : https://prove2.me/submissions/22927949-fb19-40e6-9af6-9714271b125c

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart01S0

set_option maxRecDepth 100000

/-- Chunk 10: 2 leaves. -/
theorem gt_chunk10_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_10
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 11: 2 leaves. -/
theorem gt_chunk11_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_11
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 12: 2 leaves. -/
theorem gt_chunk12_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_12
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true := by
  decide +kernel

/-- Chunk 13: 3 leaves. -/
theorem gt_chunk13_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_13
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart01S0

open BirkhoffGlobalSection.TangentialHessian.GatePart01S0 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_10 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_11 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_12 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_13 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) :=
  ⟨gt_chunk10_ok, gt_chunk11_ok, gt_chunk12_ok, gt_chunk13_ok⟩
