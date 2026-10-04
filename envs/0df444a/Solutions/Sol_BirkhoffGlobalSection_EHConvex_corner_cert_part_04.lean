-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_04
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:28.900309+00:00
-- url     : https://prove2.me/submissions/42087b28-d001-4f3f-ba25-e3e3e11f925c

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart04

set_option maxRecDepth 100000

/-- Chunk 25: 6 leaves. -/
theorem cornerK2y_chunk25_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk25
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 26: 1 leaves. -/
theorem cornerK2y_chunk26_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk26
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 27: 4 leaves. -/
theorem cornerK2y_chunk27_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk27
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 28: 8 leaves. -/
theorem cornerK2y_chunk28_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk28
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 29: 4 leaves. -/
theorem cornerK2y_chunk29_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk29
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 30: 1 leaves. -/
theorem cornerK2y_chunk30_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk30
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 31: 5 leaves. -/
theorem cornerK2y_chunk31_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk31
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 32: 8 leaves. -/
theorem cornerK2y_chunk32_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk32
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 33: 4 leaves. -/
theorem cornerK2y_chunk33_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk33
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 34: 2 leaves. -/
theorem cornerK2y_chunk34_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk34
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 35: 9 leaves. -/
theorem cornerK2y_chunk35_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk35
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 36: 1 leaves. -/
theorem cornerK2y_chunk36_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk36
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 37: 6 leaves. -/
theorem cornerK2y_chunk37_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk37
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart04

open BirkhoffGlobalSection.EHConvex.CornerPart04 in
theorem solution :
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk25 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk26 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk27 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk28 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk29 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk30 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk31 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk32 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk33 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk34 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk35 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk36 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk37 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) :=
  ⟨cornerK2y_chunk25_ok, cornerK2y_chunk26_ok, cornerK2y_chunk27_ok, cornerK2y_chunk28_ok, cornerK2y_chunk29_ok, cornerK2y_chunk30_ok, cornerK2y_chunk31_ok, cornerK2y_chunk32_ok, cornerK2y_chunk33_ok, cornerK2y_chunk34_ok, cornerK2y_chunk35_ok, cornerK2y_chunk36_ok, cornerK2y_chunk37_ok⟩
