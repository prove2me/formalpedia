-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_06
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:30.372754+00:00
-- url     : https://prove2.me/submissions/0fe81caa-9136-4d30-ae45-a023c2be3149

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart06

set_option maxRecDepth 100000

/-- Chunk 50: 8 leaves. -/
theorem cornerK2y_chunk50_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk50
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 51: 8 leaves. -/
theorem cornerK2y_chunk51_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk51
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 52: 6 leaves. -/
theorem cornerK2y_chunk52_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk52
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 53: 7 leaves. -/
theorem cornerK2y_chunk53_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk53
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 54: 6 leaves. -/
theorem cornerK2y_chunk54_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk54
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 55: 7 leaves. -/
theorem cornerK2y_chunk55_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk55
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 56: 8 leaves. -/
theorem cornerK2y_chunk56_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk56
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 57: 2 leaves. -/
theorem cornerK2y_chunk57_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk57
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 58: 1 leaves. -/
theorem cornerK2y_chunk58_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk58
      (upperHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 59: 1 leaves. -/
theorem cornerK2y_chunk59_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk59
      (upperHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 60: 8 leaves. -/
theorem cornerK2y_chunk60_ok :
    checkTree NP.centredEnc cornerK2y cornerK2y_chunk60
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart06

open BirkhoffGlobalSection.EHConvex.CornerPart06 in
theorem solution :
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk50 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk51 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk52 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk53 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk54 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk55 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk56 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk57 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk58 (upperHalf (lowerHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk59 (upperHalf (lowerHalf (upperHalf cornerK2y_box 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK2y cornerK2y_chunk60 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK2y_box 0) 1) 2) 0) 1) = true) :=
  ⟨cornerK2y_chunk50_ok, cornerK2y_chunk51_ok, cornerK2y_chunk52_ok, cornerK2y_chunk53_ok, cornerK2y_chunk54_ok, cornerK2y_chunk55_ok, cornerK2y_chunk56_ok, cornerK2y_chunk57_ok, cornerK2y_chunk58_ok, cornerK2y_chunk59_ok, cornerK2y_chunk60_ok⟩
