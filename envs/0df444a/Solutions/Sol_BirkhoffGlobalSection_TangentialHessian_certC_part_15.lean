-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_15
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:39.988984+00:00
-- url     : https://prove2.me/submissions/e6b3549c-3f0e-4059-bb9d-d63ee69ed4f9

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part15

set_option maxRecDepth 100000

/-- Chunk 225: 9 leaves. -/
theorem certC_chunk225_ok :
    checkTree NP.centredEnc certC certC_chunk225
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 226: 9 leaves. -/
theorem certC_chunk226_ok :
    checkTree NP.centredEnc certC certC_chunk226
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 227: 1 leaves. -/
theorem certC_chunk227_ok :
    checkTree NP.centredEnc certC certC_chunk227
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 228: 8 leaves. -/
theorem certC_chunk228_ok :
    checkTree NP.centredEnc certC certC_chunk228
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 229: 8 leaves. -/
theorem certC_chunk229_ok :
    checkTree NP.centredEnc certC certC_chunk229
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 230: 1 leaves. -/
theorem certC_chunk230_ok :
    checkTree NP.centredEnc certC certC_chunk230
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 231: 9 leaves. -/
theorem certC_chunk231_ok :
    checkTree NP.centredEnc certC certC_chunk231
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 232: 8 leaves. -/
theorem certC_chunk232_ok :
    checkTree NP.centredEnc certC certC_chunk232
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 233: 1 leaves. -/
theorem certC_chunk233_ok :
    checkTree NP.centredEnc certC certC_chunk233
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 234: 8 leaves. -/
theorem certC_chunk234_ok :
    checkTree NP.centredEnc certC certC_chunk234
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 235: 1 leaves. -/
theorem certC_chunk235_ok :
    checkTree NP.centredEnc certC certC_chunk235
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part15

open BirkhoffGlobalSection.TangentialHessian.Part15 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk225 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk226 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk227 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk228 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk229 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk230 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk231 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk232 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk233 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk234 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk235 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) :=
  ⟨certC_chunk225_ok, certC_chunk226_ok, certC_chunk227_ok, certC_chunk228_ok, certC_chunk229_ok, certC_chunk230_ok, certC_chunk231_ok, certC_chunk232_ok, certC_chunk233_ok, certC_chunk234_ok, certC_chunk235_ok⟩
