-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_07
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:32.757984+00:00
-- url     : https://prove2.me/submissions/828364e0-5e11-401c-a259-5b2a850bd34e

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part07

set_option maxRecDepth 100000

/-- Chunk 105: 1 leaves. -/
theorem certC_chunk105_ok :
    checkTree NP.centredEnc certC certC_chunk105
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 106: 11 leaves. -/
theorem certC_chunk106_ok :
    checkTree NP.centredEnc certC certC_chunk106
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 107: 10 leaves. -/
theorem certC_chunk107_ok :
    checkTree NP.centredEnc certC certC_chunk107
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 108: 8 leaves. -/
theorem certC_chunk108_ok :
    checkTree NP.centredEnc certC certC_chunk108
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 109: 1 leaves. -/
theorem certC_chunk109_ok :
    checkTree NP.centredEnc certC certC_chunk109
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 110: 4 leaves. -/
theorem certC_chunk110_ok :
    checkTree NP.centredEnc certC certC_chunk110
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 111: 9 leaves. -/
theorem certC_chunk111_ok :
    checkTree NP.centredEnc certC certC_chunk111
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 112: 8 leaves. -/
theorem certC_chunk112_ok :
    checkTree NP.centredEnc certC certC_chunk112
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 113: 11 leaves. -/
theorem certC_chunk113_ok :
    checkTree NP.centredEnc certC certC_chunk113
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 114: 9 leaves. -/
theorem certC_chunk114_ok :
    checkTree NP.centredEnc certC certC_chunk114
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 115: 9 leaves. -/
theorem certC_chunk115_ok :
    checkTree NP.centredEnc certC certC_chunk115
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 116: 1 leaves. -/
theorem certC_chunk116_ok :
    checkTree NP.centredEnc certC certC_chunk116
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 117: 9 leaves. -/
theorem certC_chunk117_ok :
    checkTree NP.centredEnc certC certC_chunk117
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 118: 8 leaves. -/
theorem certC_chunk118_ok :
    checkTree NP.centredEnc certC certC_chunk118
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 119: 9 leaves. -/
theorem certC_chunk119_ok :
    checkTree NP.centredEnc certC certC_chunk119
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part07

open BirkhoffGlobalSection.TangentialHessian.Part07 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk105 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk106 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk107 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk108 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk109 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk110 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk111 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk112 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk113 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk114 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk115 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk116 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk117 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk118 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk119 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) :=
  ⟨certC_chunk105_ok, certC_chunk106_ok, certC_chunk107_ok, certC_chunk108_ok, certC_chunk109_ok, certC_chunk110_ok, certC_chunk111_ok, certC_chunk112_ok, certC_chunk113_ok, certC_chunk114_ok, certC_chunk115_ok, certC_chunk116_ok, certC_chunk117_ok, certC_chunk118_ok, certC_chunk119_ok⟩
