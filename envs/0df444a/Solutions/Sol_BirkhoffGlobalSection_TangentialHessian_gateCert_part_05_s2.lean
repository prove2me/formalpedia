-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_05_s2
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:34.628138+00:00
-- url     : https://prove2.me/submissions/c0129c46-b880-4d32-b254-237cec84f540

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart05S2

set_option maxRecDepth 100000

/-- Chunk 66: 2 leaves. -/
theorem gt_chunk66_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_66
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart05S2

open BirkhoffGlobalSection.TangentialHessian.GatePart05S2 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_66 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) :=
  gt_chunk66_ok
