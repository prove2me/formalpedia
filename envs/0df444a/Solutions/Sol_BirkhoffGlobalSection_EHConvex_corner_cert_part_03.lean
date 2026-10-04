-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_03
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:28.106972+00:00
-- url     : https://prove2.me/submissions/f55fdd00-caf3-4ee7-8cf0-20d7b2faf370

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart03

set_option maxRecDepth 100000

/-- Chunk 12: 10 leaves. -/
theorem cornerK2y_chunk12_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk12
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 13: 7 leaves. -/
theorem cornerK2y_chunk13_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk13
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 14: 1 leaves. -/
theorem cornerK2y_chunk14_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk14
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 15: 1 leaves. -/
theorem cornerK2y_chunk15_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk15
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 16: 7 leaves. -/
theorem cornerK2y_chunk16_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk16
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 17: 3 leaves. -/
theorem cornerK2y_chunk17_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk17
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 18: 9 leaves. -/
theorem cornerK2y_chunk18_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk18
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 19: 2 leaves. -/
theorem cornerK2y_chunk19_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk19
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 20: 3 leaves. -/
theorem cornerK2y_chunk20_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk20
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 21: 8 leaves. -/
theorem cornerK2y_chunk21_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk21
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 22: 1 leaves. -/
theorem cornerK2y_chunk22_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk22
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 23: 1 leaves. -/
theorem cornerK2y_chunk23_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk23
      (upperHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 24: 10 leaves. -/
theorem cornerK2y_chunk24_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk24
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart03

open BirkhoffGlobalSection.EHConvex.CornerPart03 in
theorem solution :
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk12 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk13 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk14 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk15 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk16 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk17 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk18 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk19 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk20 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk21 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk22 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk23 (upperHalf (lowerHalf (lowerHalf cornerK2y_box 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk24 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) :=
  ⟨cornerK2y_chunk12_ok, cornerK2y_chunk13_ok, cornerK2y_chunk14_ok, cornerK2y_chunk15_ok, cornerK2y_chunk16_ok, cornerK2y_chunk17_ok, cornerK2y_chunk18_ok, cornerK2y_chunk19_ok, cornerK2y_chunk20_ok, cornerK2y_chunk21_ok, cornerK2y_chunk22_ok, cornerK2y_chunk23_ok, cornerK2y_chunk24_ok⟩
