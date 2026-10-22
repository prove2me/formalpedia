-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s2
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:30.208533+00:00
-- url     : https://prove2.me/submissions/fa9c1212-11ba-41ce-955e-01fb8c556641

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart01S2

set_option maxRecDepth 100000

/-- Chunk 18: 2 leaves. -/
theorem gt_chunk18_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_18
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true := by
  decide +kernel

/-- Chunk 19: 2 leaves. -/
theorem gt_chunk19_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_19
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 20: 2 leaves. -/
theorem gt_chunk20_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_20
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart01S2

open BirkhoffGlobalSection.TangentialHessian.GatePart01S2 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_18 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_19 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_20 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) :=
  ⟨gt_chunk18_ok, gt_chunk19_ok, gt_chunk20_ok⟩
