-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.gateCert_part_29
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T17:59:51.768705+00:00
-- url     : https://prove2.me/submissions/59fff073-e1db-4eff-b748-aff18fb3c886

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian.GatePart29

set_option maxRecDepth 100000

/-- Chunk 304: 2 leaves. -/
theorem gt_chunk304_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_304
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 305: 1 leaves. -/
theorem gt_chunk305_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_305
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 306: 2 leaves. -/
theorem gt_chunk306_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_306
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 307: 2 leaves. -/
theorem gt_chunk307_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_307
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 308: 2 leaves. -/
theorem gt_chunk308_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_308
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 309: 3 leaves. -/
theorem gt_chunk309_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_309
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true := by
  decide +kernel

/-- Chunk 310: 1 leaves. -/
theorem gt_chunk310_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_310
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true := by
  decide +kernel

/-- Chunk 311: 1 leaves. -/
theorem gt_chunk311_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_311
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 312: 2 leaves. -/
theorem gt_chunk312_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_312
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

/-- Chunk 313: 2 leaves. -/
theorem gt_chunk313_ok :
    checkTree GQ.enc (gateCert gt_tree) gtc_313
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.GatePart29

open BirkhoffGlobalSection.TangentialHessian.GatePart29 in
theorem solution :
    (checkTree GQ.enc (gateCert gt_tree) gtc_304 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_305 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_306 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_307 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_308 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_309 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_310 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_311 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_312 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_313 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) :=
  ⟨gt_chunk304_ok, gt_chunk305_ok, gt_chunk306_ok, gt_chunk307_ok, gt_chunk308_ok, gt_chunk309_ok, gt_chunk310_ok, gt_chunk311_ok, gt_chunk312_ok, gt_chunk313_ok⟩
