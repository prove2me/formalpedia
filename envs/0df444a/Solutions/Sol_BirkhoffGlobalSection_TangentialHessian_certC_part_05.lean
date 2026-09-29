-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_05
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:31.27498+00:00
-- url     : https://prove2.me/submissions/9eea39b4-5c1e-4163-9da7-cf0a7323c150

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part05

set_option maxRecDepth 100000

/-- Chunk 75: 7 leaves. -/
theorem certC_chunk75_ok :
    checkTree NP.centredEnc certC certC_chunk75
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 76: 8 leaves. -/
theorem certC_chunk76_ok :
    checkTree NP.centredEnc certC certC_chunk76
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 77: 9 leaves. -/
theorem certC_chunk77_ok :
    checkTree NP.centredEnc certC certC_chunk77
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 78: 6 leaves. -/
theorem certC_chunk78_ok :
    checkTree NP.centredEnc certC certC_chunk78
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 79: 8 leaves. -/
theorem certC_chunk79_ok :
    checkTree NP.centredEnc certC certC_chunk79
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 80: 6 leaves. -/
theorem certC_chunk80_ok :
    checkTree NP.centredEnc certC certC_chunk80
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 81: 7 leaves. -/
theorem certC_chunk81_ok :
    checkTree NP.centredEnc certC certC_chunk81
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 82: 1 leaves. -/
theorem certC_chunk82_ok :
    checkTree NP.centredEnc certC certC_chunk82
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 83: 8 leaves. -/
theorem certC_chunk83_ok :
    checkTree NP.centredEnc certC certC_chunk83
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 84: 8 leaves. -/
theorem certC_chunk84_ok :
    checkTree NP.centredEnc certC certC_chunk84
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 85: 8 leaves. -/
theorem certC_chunk85_ok :
    checkTree NP.centredEnc certC certC_chunk85
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 86: 7 leaves. -/
theorem certC_chunk86_ok :
    checkTree NP.centredEnc certC certC_chunk86
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 87: 9 leaves. -/
theorem certC_chunk87_ok :
    checkTree NP.centredEnc certC certC_chunk87
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 88: 1 leaves. -/
theorem certC_chunk88_ok :
    checkTree NP.centredEnc certC certC_chunk88
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 89: 11 leaves. -/
theorem certC_chunk89_ok :
    checkTree NP.centredEnc certC certC_chunk89
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part05

open BirkhoffGlobalSection.TangentialHessian.Part05 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk75 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk76 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk77 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk78 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk79 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk80 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk81 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk82 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk83 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk84 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk85 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk86 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk87 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk88 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk89 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) :=
  ⟨certC_chunk75_ok, certC_chunk76_ok, certC_chunk77_ok, certC_chunk78_ok, certC_chunk79_ok, certC_chunk80_ok, certC_chunk81_ok, certC_chunk82_ok, certC_chunk83_ok, certC_chunk84_ok, certC_chunk85_ok, certC_chunk86_ok, certC_chunk87_ok, certC_chunk88_ok, certC_chunk89_ok⟩
