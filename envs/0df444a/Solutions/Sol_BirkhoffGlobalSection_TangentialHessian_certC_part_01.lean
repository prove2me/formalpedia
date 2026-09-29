-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_01
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:27.747605+00:00
-- url     : https://prove2.me/submissions/fb8ee2eb-a891-420f-a7d0-34f9e407bb6f

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part01

set_option maxRecDepth 100000

/-- Chunk 15: 8 leaves. -/
theorem certC_chunk15_ok :
    checkTree NP.centredEnc certC certC_chunk15
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 16: 8 leaves. -/
theorem certC_chunk16_ok :
    checkTree NP.centredEnc certC certC_chunk16
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 17: 11 leaves. -/
theorem certC_chunk17_ok :
    checkTree NP.centredEnc certC certC_chunk17
      (lowerHalf (lowerHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 18: 8 leaves. -/
theorem certC_chunk18_ok :
    checkTree NP.centredEnc certC certC_chunk18
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 19: 6 leaves. -/
theorem certC_chunk19_ok :
    checkTree NP.centredEnc certC certC_chunk19
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 20: 7 leaves. -/
theorem certC_chunk20_ok :
    checkTree NP.centredEnc certC certC_chunk20
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 21: 8 leaves. -/
theorem certC_chunk21_ok :
    checkTree NP.centredEnc certC certC_chunk21
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 22: 7 leaves. -/
theorem certC_chunk22_ok :
    checkTree NP.centredEnc certC certC_chunk22
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 23: 7 leaves. -/
theorem certC_chunk23_ok :
    checkTree NP.centredEnc certC certC_chunk23
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 24: 1 leaves. -/
theorem certC_chunk24_ok :
    checkTree NP.centredEnc certC certC_chunk24
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 25: 12 leaves. -/
theorem certC_chunk25_ok :
    checkTree NP.centredEnc certC certC_chunk25
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 26: 8 leaves. -/
theorem certC_chunk26_ok :
    checkTree NP.centredEnc certC certC_chunk26
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 27: 8 leaves. -/
theorem certC_chunk27_ok :
    checkTree NP.centredEnc certC certC_chunk27
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 28: 8 leaves. -/
theorem certC_chunk28_ok :
    checkTree NP.centredEnc certC certC_chunk28
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 29: 9 leaves. -/
theorem certC_chunk29_ok :
    checkTree NP.centredEnc certC certC_chunk29
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part01

open BirkhoffGlobalSection.TangentialHessian.Part01 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk15 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk16 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk17 (lowerHalf (lowerHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk18 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk19 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk20 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk21 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk22 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk23 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk24 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk25 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk26 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk27 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk28 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk29 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) :=
  ⟨certC_chunk15_ok, certC_chunk16_ok, certC_chunk17_ok, certC_chunk18_ok, certC_chunk19_ok, certC_chunk20_ok, certC_chunk21_ok, certC_chunk22_ok, certC_chunk23_ok, certC_chunk24_ok, certC_chunk25_ok, certC_chunk26_ok, certC_chunk27_ok, certC_chunk28_ok, certC_chunk29_ok⟩
