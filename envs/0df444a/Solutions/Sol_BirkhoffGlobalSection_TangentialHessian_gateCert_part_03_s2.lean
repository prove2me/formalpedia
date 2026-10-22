-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_03_s2
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:29.64556+00:00
-- url     : https://prove2.me/submissions/51df1add-991c-4ea3-9b78-fdd500699537

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart03S2

set_option maxRecDepth 100000

/-- Chunk 42: 2 leaves. -/
theorem gt_chunk42_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_42
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 43: 2 leaves. -/
theorem gt_chunk43_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_43
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart03S2

open BirkhoffGlobalSection.TangentialHessian.GatePart03S2 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_42 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_43 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) :=
  ⟨gt_chunk42_ok, gt_chunk43_ok⟩
