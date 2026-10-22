-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_00_s1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T22:26:26.493498+00:00
-- url     : https://prove2.me/submissions/9cb29c23-8614-4917-8b58-8dab03b89c3b

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart00S1

set_option maxRecDepth 100000

/-- Chunk 4: 4 leaves. -/
theorem gt_chunk4_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_4
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) = true := by
  decide +kernel

/-- Chunk 5: 3 leaves. -/
theorem gt_chunk5_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_5
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 6: 2 leaves. -/
theorem gt_chunk6_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_6
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 7: 2 leaves. -/
theorem gt_chunk7_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_7
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) 1) = true := by
  decide +kernel

/-- Chunk 8: 2 leaves. -/
theorem gt_chunk8_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_8
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart00S1

open BirkhoffGlobalSection.TangentialHessian.GatePart00S1 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_4 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_5 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_6 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_7 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_8 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true) :=
  ⟨gt_chunk4_ok, gt_chunk5_ok, gt_chunk6_ok, gt_chunk7_ok, gt_chunk8_ok⟩
