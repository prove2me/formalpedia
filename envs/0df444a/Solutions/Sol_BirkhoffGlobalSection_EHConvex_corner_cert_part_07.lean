-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_07
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:31.281725+00:00
-- url     : https://prove2.me/submissions/ecc7c397-72ed-4e75-a87c-25140c36a50e

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart07

set_option maxRecDepth 100000

/-- Chunk 61: 5 leaves. -/
theorem cornerK2y_chunk61_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk61
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 62: 1 leaves. -/
theorem cornerK2y_chunk62_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk62
      (upperHalf (lowerHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 63: 9 leaves. -/
theorem cornerK2y_chunk63_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk63
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 64: 3 leaves. -/
theorem cornerK2y_chunk64_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk64
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 65: 5 leaves. -/
theorem cornerK2y_chunk65_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk65
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 66: 6 leaves. -/
theorem cornerK2y_chunk66_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk66
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 67: 7 leaves. -/
theorem cornerK2y_chunk67_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk67
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 68: 4 leaves. -/
theorem cornerK2y_chunk68_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk68
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 69: 1 leaves. -/
theorem cornerK2y_chunk69_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk69
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 70: 5 leaves. -/
theorem cornerK2y_chunk70_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk70
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 71: 9 leaves. -/
theorem cornerK2y_chunk71_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk71
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 72: 4 leaves. -/
theorem cornerK2y_chunk72_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk72
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart07

open BirkhoffGlobalSection.EHConvex.CornerPart07 in
theorem solution :
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk61 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk62 (upperHalf (lowerHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk63 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk64 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk65 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk66 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk67 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk68 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk69 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk70 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk71 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk72 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) :=
  ⟨cornerK2y_chunk61_ok, cornerK2y_chunk62_ok, cornerK2y_chunk63_ok, cornerK2y_chunk64_ok, cornerK2y_chunk65_ok, cornerK2y_chunk66_ok, cornerK2y_chunk67_ok, cornerK2y_chunk68_ok, cornerK2y_chunk69_ok, cornerK2y_chunk70_ok, cornerK2y_chunk71_ok, cornerK2y_chunk72_ok⟩
