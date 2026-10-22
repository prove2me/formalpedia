-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_00_s2
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:40:26.626716+00:00
-- url     : https://prove2.me/submissions/a96f4bd8-feca-42c1-93c7-b9f4f3eb2582

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart00S2

set_option maxRecDepth 100000

/-- Chunk 9: 3 leaves. -/
theorem gt_chunk9_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_9
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart00S2

open BirkhoffGlobalSection.TangentialHessian.GatePart00S2 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_9 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true) :=
  gt_chunk9_ok
