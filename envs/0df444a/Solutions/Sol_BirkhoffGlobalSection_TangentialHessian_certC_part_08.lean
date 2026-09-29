-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_08
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:33.624987+00:00
-- url     : https://prove2.me/submissions/7c2dad87-500a-4a18-b846-5582d5938130

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part08

set_option maxRecDepth 100000

/-- Chunk 120: 9 leaves. -/
theorem certC_chunk120_ok :
    checkTree NP.centredEnc certC certC_chunk120
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 121: 8 leaves. -/
theorem certC_chunk121_ok :
    checkTree NP.centredEnc certC certC_chunk121
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 122: 9 leaves. -/
theorem certC_chunk122_ok :
    checkTree NP.centredEnc certC certC_chunk122
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 123: 9 leaves. -/
theorem certC_chunk123_ok :
    checkTree NP.centredEnc certC certC_chunk123
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 124: 9 leaves. -/
theorem certC_chunk124_ok :
    checkTree NP.centredEnc certC certC_chunk124
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 125: 1 leaves. -/
theorem certC_chunk125_ok :
    checkTree NP.centredEnc certC certC_chunk125
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 126: 9 leaves. -/
theorem certC_chunk126_ok :
    checkTree NP.centredEnc certC certC_chunk126
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 127: 9 leaves. -/
theorem certC_chunk127_ok :
    checkTree NP.centredEnc certC certC_chunk127
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 128: 9 leaves. -/
theorem certC_chunk128_ok :
    checkTree NP.centredEnc certC certC_chunk128
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 129: 9 leaves. -/
theorem certC_chunk129_ok :
    checkTree NP.centredEnc certC certC_chunk129
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 130: 1 leaves. -/
theorem certC_chunk130_ok :
    checkTree NP.centredEnc certC certC_chunk130
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 131: 12 leaves. -/
theorem certC_chunk131_ok :
    checkTree NP.centredEnc certC certC_chunk131
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 132: 1 leaves. -/
theorem certC_chunk132_ok :
    checkTree NP.centredEnc certC certC_chunk132
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 133: 7 leaves. -/
theorem certC_chunk133_ok :
    checkTree NP.centredEnc certC certC_chunk133
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 134: 8 leaves. -/
theorem certC_chunk134_ok :
    checkTree NP.centredEnc certC certC_chunk134
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part08

open BirkhoffGlobalSection.TangentialHessian.Part08 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk120 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk121 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk122 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk123 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk124 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk125 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk126 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk127 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk128 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk129 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk130 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk131 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk132 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk133 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk134 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) :=
  ⟨certC_chunk120_ok, certC_chunk121_ok, certC_chunk122_ok, certC_chunk123_ok, certC_chunk124_ok, certC_chunk125_ok, certC_chunk126_ok, certC_chunk127_ok, certC_chunk128_ok, certC_chunk129_ok, certC_chunk130_ok, certC_chunk131_ok, certC_chunk132_ok, certC_chunk133_ok, certC_chunk134_ok⟩
