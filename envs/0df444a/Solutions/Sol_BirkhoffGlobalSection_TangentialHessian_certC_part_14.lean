-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_14
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:39.125879+00:00
-- url     : https://prove2.me/submissions/22502e9e-cb6a-496c-8042-c99086198afc

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part14

set_option maxRecDepth 100000

/-- Chunk 210: 9 leaves. -/
theorem certC_chunk210_ok :
    checkTree NP.centredEnc certC certC_chunk210
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 211: 1 leaves. -/
theorem certC_chunk211_ok :
    checkTree NP.centredEnc certC certC_chunk211
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 212: 6 leaves. -/
theorem certC_chunk212_ok :
    checkTree NP.centredEnc certC certC_chunk212
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 213: 7 leaves. -/
theorem certC_chunk213_ok :
    checkTree NP.centredEnc certC certC_chunk213
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 214: 1 leaves. -/
theorem certC_chunk214_ok :
    checkTree NP.centredEnc certC certC_chunk214
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 215: 8 leaves. -/
theorem certC_chunk215_ok :
    checkTree NP.centredEnc certC certC_chunk215
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 216: 7 leaves. -/
theorem certC_chunk216_ok :
    checkTree NP.centredEnc certC certC_chunk216
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 217: 1 leaves. -/
theorem certC_chunk217_ok :
    checkTree NP.centredEnc certC certC_chunk217
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 218: 10 leaves. -/
theorem certC_chunk218_ok :
    checkTree NP.centredEnc certC certC_chunk218
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 219: 5 leaves. -/
theorem certC_chunk219_ok :
    checkTree NP.centredEnc certC certC_chunk219
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 220: 8 leaves. -/
theorem certC_chunk220_ok :
    checkTree NP.centredEnc certC certC_chunk220
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 221: 7 leaves. -/
theorem certC_chunk221_ok :
    checkTree NP.centredEnc certC certC_chunk221
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 222: 9 leaves. -/
theorem certC_chunk222_ok :
    checkTree NP.centredEnc certC certC_chunk222
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 223: 1 leaves. -/
theorem certC_chunk223_ok :
    checkTree NP.centredEnc certC certC_chunk223
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 224: 1 leaves. -/
theorem certC_chunk224_ok :
    checkTree NP.centredEnc certC certC_chunk224
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part14

open BirkhoffGlobalSection.TangentialHessian.Part14 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk210 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk211 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk212 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk213 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk214 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk215 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk216 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk217 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk218 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk219 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk220 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk221 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk222 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk223 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk224 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) :=
  ⟨certC_chunk210_ok, certC_chunk211_ok, certC_chunk212_ok, certC_chunk213_ok, certC_chunk214_ok, certC_chunk215_ok, certC_chunk216_ok, certC_chunk217_ok, certC_chunk218_ok, certC_chunk219_ok, certC_chunk220_ok, certC_chunk221_ok, certC_chunk222_ok, certC_chunk223_ok, certC_chunk224_ok⟩
