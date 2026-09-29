-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_06
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:31.976337+00:00
-- url     : https://prove2.me/submissions/3bc8799c-bb6f-4aa1-bfe4-9d5545254c77

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part06

set_option maxRecDepth 100000

/-- Chunk 90: 8 leaves. -/
theorem certC_chunk90_ok :
    checkTree NP.centredEnc certC certC_chunk90
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 91: 8 leaves. -/
theorem certC_chunk91_ok :
    checkTree NP.centredEnc certC certC_chunk91
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 92: 1 leaves. -/
theorem certC_chunk92_ok :
    checkTree NP.centredEnc certC certC_chunk92
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 93: 12 leaves. -/
theorem certC_chunk93_ok :
    checkTree NP.centredEnc certC certC_chunk93
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 94: 8 leaves. -/
theorem certC_chunk94_ok :
    checkTree NP.centredEnc certC certC_chunk94
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 95: 10 leaves. -/
theorem certC_chunk95_ok :
    checkTree NP.centredEnc certC certC_chunk95
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 96: 9 leaves. -/
theorem certC_chunk96_ok :
    checkTree NP.centredEnc certC certC_chunk96
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 97: 9 leaves. -/
theorem certC_chunk97_ok :
    checkTree NP.centredEnc certC certC_chunk97
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 98: 1 leaves. -/
theorem certC_chunk98_ok :
    checkTree NP.centredEnc certC certC_chunk98
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 99: 8 leaves. -/
theorem certC_chunk99_ok :
    checkTree NP.centredEnc certC certC_chunk99
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 100: 9 leaves. -/
theorem certC_chunk100_ok :
    checkTree NP.centredEnc certC certC_chunk100
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 101: 8 leaves. -/
theorem certC_chunk101_ok :
    checkTree NP.centredEnc certC certC_chunk101
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 102: 7 leaves. -/
theorem certC_chunk102_ok :
    checkTree NP.centredEnc certC certC_chunk102
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 103: 9 leaves. -/
theorem certC_chunk103_ok :
    checkTree NP.centredEnc certC certC_chunk103
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 104: 9 leaves. -/
theorem certC_chunk104_ok :
    checkTree NP.centredEnc certC certC_chunk104
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part06

open BirkhoffGlobalSection.TangentialHessian.Part06 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk90 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk91 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk92 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk93 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk94 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk95 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk96 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk97 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk98 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk99 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk100 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk101 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk102 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk103 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk104 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) :=
  ⟨certC_chunk90_ok, certC_chunk91_ok, certC_chunk92_ok, certC_chunk93_ok, certC_chunk94_ok, certC_chunk95_ok, certC_chunk96_ok, certC_chunk97_ok, certC_chunk98_ok, certC_chunk99_ok, certC_chunk100_ok, certC_chunk101_ok, certC_chunk102_ok, certC_chunk103_ok, certC_chunk104_ok⟩
