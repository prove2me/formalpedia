-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_03
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:29.593142+00:00
-- url     : https://prove2.me/submissions/39dfeeff-5a24-4e0f-8aaa-de7ba00ce567

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part03

set_option maxRecDepth 100000

/-- Chunk 45: 8 leaves. -/
theorem certC_chunk45_ok :
    checkTree NP.centredEnc certC certC_chunk45
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 46: 8 leaves. -/
theorem certC_chunk46_ok :
    checkTree NP.centredEnc certC certC_chunk46
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 47: 9 leaves. -/
theorem certC_chunk47_ok :
    checkTree NP.centredEnc certC certC_chunk47
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 48: 8 leaves. -/
theorem certC_chunk48_ok :
    checkTree NP.centredEnc certC certC_chunk48
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 49: 6 leaves. -/
theorem certC_chunk49_ok :
    checkTree NP.centredEnc certC certC_chunk49
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 50: 7 leaves. -/
theorem certC_chunk50_ok :
    checkTree NP.centredEnc certC certC_chunk50
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 51: 10 leaves. -/
theorem certC_chunk51_ok :
    checkTree NP.centredEnc certC certC_chunk51
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 52: 8 leaves. -/
theorem certC_chunk52_ok :
    checkTree NP.centredEnc certC certC_chunk52
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 53: 8 leaves. -/
theorem certC_chunk53_ok :
    checkTree NP.centredEnc certC certC_chunk53
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 54: 8 leaves. -/
theorem certC_chunk54_ok :
    checkTree NP.centredEnc certC certC_chunk54
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 55: 2 leaves. -/
theorem certC_chunk55_ok :
    checkTree NP.centredEnc certC certC_chunk55
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 56: 8 leaves. -/
theorem certC_chunk56_ok :
    checkTree NP.centredEnc certC certC_chunk56
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 57: 12 leaves. -/
theorem certC_chunk57_ok :
    checkTree NP.centredEnc certC certC_chunk57
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 58: 1 leaves. -/
theorem certC_chunk58_ok :
    checkTree NP.centredEnc certC certC_chunk58
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 59: 8 leaves. -/
theorem certC_chunk59_ok :
    checkTree NP.centredEnc certC certC_chunk59
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part03

open BirkhoffGlobalSection.TangentialHessian.Part03 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk45 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk46 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk47 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk48 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk49 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk50 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk51 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk52 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk53 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk54 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk55 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk56 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk57 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk58 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk59 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) :=
  ⟨certC_chunk45_ok, certC_chunk46_ok, certC_chunk47_ok, certC_chunk48_ok, certC_chunk49_ok, certC_chunk50_ok, certC_chunk51_ok, certC_chunk52_ok, certC_chunk53_ok, certC_chunk54_ok, certC_chunk55_ok, certC_chunk56_ok, certC_chunk57_ok, certC_chunk58_ok, certC_chunk59_ok⟩
