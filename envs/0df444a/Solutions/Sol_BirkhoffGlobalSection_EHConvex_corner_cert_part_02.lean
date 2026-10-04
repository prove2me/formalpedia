-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_02
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:27.330257+00:00
-- url     : https://prove2.me/submissions/9f376dfe-3bad-469d-8cf2-b88b5638a1e3

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart02

set_option maxRecDepth 100000

/-- Chunk 0: 7 leaves. -/
theorem cornerK2y_chunk0_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk0
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 1: 5 leaves. -/
theorem cornerK2y_chunk1_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk1
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 2: 5 leaves. -/
theorem cornerK2y_chunk2_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk2
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 3: 4 leaves. -/
theorem cornerK2y_chunk3_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk3
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 4: 10 leaves. -/
theorem cornerK2y_chunk4_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk4
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 5: 1 leaves. -/
theorem cornerK2y_chunk5_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk5
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 6: 7 leaves. -/
theorem cornerK2y_chunk6_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk6
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 7: 1 leaves. -/
theorem cornerK2y_chunk7_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk7
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 8: 3 leaves. -/
theorem cornerK2y_chunk8_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk8
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 9: 10 leaves. -/
theorem cornerK2y_chunk9_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk9
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 10: 1 leaves. -/
theorem cornerK2y_chunk10_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk10
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 11: 3 leaves. -/
theorem cornerK2y_chunk11_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk11
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart02

open BirkhoffGlobalSection.EHConvex.CornerPart02 in
theorem solution :
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk0 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk1 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk2 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk3 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk4 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk5 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk6 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk7 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk8 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk9 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk10 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk11 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) :=
  ⟨cornerK2y_chunk0_ok, cornerK2y_chunk1_ok, cornerK2y_chunk2_ok, cornerK2y_chunk3_ok, cornerK2y_chunk4_ok, cornerK2y_chunk5_ok, cornerK2y_chunk6_ok, cornerK2y_chunk7_ok, cornerK2y_chunk8_ok, cornerK2y_chunk9_ok, cornerK2y_chunk10_ok, cornerK2y_chunk11_ok⟩
