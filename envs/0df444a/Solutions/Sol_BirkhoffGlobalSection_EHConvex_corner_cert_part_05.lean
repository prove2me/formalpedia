-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_05
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:29.628613+00:00
-- url     : https://prove2.me/submissions/c5c3e1c1-8727-47e5-92a7-355636b821c3

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart05

set_option maxRecDepth 100000

/-- Chunk 38: 8 leaves. -/
theorem cornerK2y_chunk38_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk38
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 39: 9 leaves. -/
theorem cornerK2y_chunk39_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk39
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 40: 4 leaves. -/
theorem cornerK2y_chunk40_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk40
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 41: 5 leaves. -/
theorem cornerK2y_chunk41_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk41
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 42: 7 leaves. -/
theorem cornerK2y_chunk42_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk42
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 43: 8 leaves. -/
theorem cornerK2y_chunk43_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk43
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 44: 3 leaves. -/
theorem cornerK2y_chunk44_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk44
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 45: 8 leaves. -/
theorem cornerK2y_chunk45_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk45
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 46: 5 leaves. -/
theorem cornerK2y_chunk46_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk46
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 47: 1 leaves. -/
theorem cornerK2y_chunk47_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk47
      (lowerHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 48: 1 leaves. -/
theorem cornerK2y_chunk48_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk48
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 49: 5 leaves. -/
theorem cornerK2y_chunk49_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk49
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart05

open BirkhoffGlobalSection.EHConvex.CornerPart05 in
theorem solution :
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk38 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk39 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk40 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk41 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk42 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk43 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk44 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk45 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk46 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk47 (lowerHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk48 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk49 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) :=
  ⟨cornerK2y_chunk38_ok, cornerK2y_chunk39_ok, cornerK2y_chunk40_ok, cornerK2y_chunk41_ok, cornerK2y_chunk42_ok, cornerK2y_chunk43_ok, cornerK2y_chunk44_ok, cornerK2y_chunk45_ok, cornerK2y_chunk46_ok, cornerK2y_chunk47_ok, cornerK2y_chunk48_ok, cornerK2y_chunk49_ok⟩
