-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_04
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:30.344981+00:00
-- url     : https://prove2.me/submissions/44662fbd-8d12-4af0-8e44-c96189b20235

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part04

set_option maxRecDepth 100000

/-- Chunk 60: 8 leaves. -/
theorem certC_chunk60_ok :
    checkTree NP.centredEnc certC certC_chunk60
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 61: 9 leaves. -/
theorem certC_chunk61_ok :
    checkTree NP.centredEnc certC certC_chunk61
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 62: 9 leaves. -/
theorem certC_chunk62_ok :
    checkTree NP.centredEnc certC certC_chunk62
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 63: 1 leaves. -/
theorem certC_chunk63_ok :
    checkTree NP.centredEnc certC certC_chunk63
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 64: 12 leaves. -/
theorem certC_chunk64_ok :
    checkTree NP.centredEnc certC certC_chunk64
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 65: 9 leaves. -/
theorem certC_chunk65_ok :
    checkTree NP.centredEnc certC certC_chunk65
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 66: 5 leaves. -/
theorem certC_chunk66_ok :
    checkTree NP.centredEnc certC certC_chunk66
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 67: 8 leaves. -/
theorem certC_chunk67_ok :
    checkTree NP.centredEnc certC certC_chunk67
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 68: 8 leaves. -/
theorem certC_chunk68_ok :
    checkTree NP.centredEnc certC certC_chunk68
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 69: 9 leaves. -/
theorem certC_chunk69_ok :
    checkTree NP.centredEnc certC certC_chunk69
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 70: 9 leaves. -/
theorem certC_chunk70_ok :
    checkTree NP.centredEnc certC certC_chunk70
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 71: 1 leaves. -/
theorem certC_chunk71_ok :
    checkTree NP.centredEnc certC certC_chunk71
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 72: 9 leaves. -/
theorem certC_chunk72_ok :
    checkTree NP.centredEnc certC certC_chunk72
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 73: 6 leaves. -/
theorem certC_chunk73_ok :
    checkTree NP.centredEnc certC certC_chunk73
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 74: 9 leaves. -/
theorem certC_chunk74_ok :
    checkTree NP.centredEnc certC certC_chunk74
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part04

open BirkhoffGlobalSection.TangentialHessian.Part04 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk60 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk61 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk62 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk63 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk64 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk65 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk66 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk67 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk68 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk69 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk70 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk71 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk72 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk73 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk74 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) :=
  ⟨certC_chunk60_ok, certC_chunk61_ok, certC_chunk62_ok, certC_chunk63_ok, certC_chunk64_ok, certC_chunk65_ok, certC_chunk66_ok, certC_chunk67_ok, certC_chunk68_ok, certC_chunk69_ok, certC_chunk70_ok, certC_chunk71_ok, certC_chunk72_ok, certC_chunk73_ok, certC_chunk74_ok⟩
