-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_08
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:32.005983+00:00
-- url     : https://prove2.me/submissions/bc933f73-e6ae-4dcd-9088-96e31270204d

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart08

set_option maxRecDepth 100000

/-- Chunk 73: 10 leaves. -/
theorem cornerK2y_chunk73_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk73
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 74: 7 leaves. -/
theorem cornerK2y_chunk74_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk74
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 75: 10 leaves. -/
theorem cornerK2y_chunk75_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk75
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 76: 1 leaves. -/
theorem cornerK2y_chunk76_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk76
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 77: 1 leaves. -/
theorem cornerK2y_chunk77_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk77
      (upperHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart08

open BirkhoffGlobalSection.EHConvex.CornerPart08 in
theorem solution :
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk73 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk74 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk75 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk76 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk77 (upperHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) = true) :=
  ⟨cornerK2y_chunk73_ok, cornerK2y_chunk74_ok, cornerK2y_chunk75_ok, cornerK2y_chunk76_ok, cornerK2y_chunk77_ok⟩
