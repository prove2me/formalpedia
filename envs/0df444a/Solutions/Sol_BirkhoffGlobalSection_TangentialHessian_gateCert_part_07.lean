-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_07
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T18:27:41.845216+00:00
-- url     : https://prove2.me/submissions/ef6de860-16d5-4995-a919-971fb64c90e9

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart07

set_option maxRecDepth 100000

/-- Chunk 76: 2 leaves. -/
theorem gt_chunk76_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_76
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 0) = true := by
  decide +kernel

/-- Chunk 77: 2 leaves. -/
theorem gt_chunk77_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_77
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 78: 2 leaves. -/
theorem gt_chunk78_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_78
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 79: 3 leaves. -/
theorem gt_chunk79_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_79
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 80: 2 leaves. -/
theorem gt_chunk80_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_80
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 81: 2 leaves. -/
theorem gt_chunk81_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_81
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 82: 2 leaves. -/
theorem gt_chunk82_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_82
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 83: 3 leaves. -/
theorem gt_chunk83_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_83
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true := by
  decide +kernel

/-- Chunk 84: 3 leaves. -/
theorem gt_chunk84_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_84
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart07

open BirkhoffGlobalSection.TangentialHessian.GatePart07 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_76 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_77 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_78 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_79 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_80 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_81 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_82 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_83 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_84 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) :=
  ⟨gt_chunk76_ok, gt_chunk77_ok, gt_chunk78_ok, gt_chunk79_ok, gt_chunk80_ok, gt_chunk81_ok, gt_chunk82_ok, gt_chunk83_ok, gt_chunk84_ok⟩
