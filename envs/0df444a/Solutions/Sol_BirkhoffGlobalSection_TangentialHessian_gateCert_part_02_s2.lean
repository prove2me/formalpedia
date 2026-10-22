-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_02_s2
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:32.648779+00:00
-- url     : https://prove2.me/submissions/63c30562-4ada-4c15-9866-1f4d56e0bfe0

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart02S2

set_option maxRecDepth 100000

/-- Chunk 31: 2 leaves. -/
theorem gt_chunk31_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_31
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 32: 2 leaves. -/
theorem gt_chunk32_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_32
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart02S2

open BirkhoffGlobalSection.TangentialHessian.GatePart02S2 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_31 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_32 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) :=
  ⟨gt_chunk31_ok, gt_chunk32_ok⟩
