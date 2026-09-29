-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_12
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:37.294931+00:00
-- url     : https://prove2.me/submissions/92bc1785-3f93-4dc1-ba0b-258f72ebe354

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part12

set_option maxRecDepth 100000

/-- Chunk 180: 4 leaves. -/
theorem certC_chunk180_ok :
    checkTree NP.centredEnc certC certC_chunk180
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 181: 11 leaves. -/
theorem certC_chunk181_ok :
    checkTree NP.centredEnc certC certC_chunk181
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 182: 12 leaves. -/
theorem certC_chunk182_ok :
    checkTree NP.centredEnc certC certC_chunk182
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 183: 1 leaves. -/
theorem certC_chunk183_ok :
    checkTree NP.centredEnc certC certC_chunk183
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 184: 1 leaves. -/
theorem certC_chunk184_ok :
    checkTree NP.centredEnc certC certC_chunk184
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 185: 1 leaves. -/
theorem certC_chunk185_ok :
    checkTree NP.centredEnc certC certC_chunk185
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 186: 8 leaves. -/
theorem certC_chunk186_ok :
    checkTree NP.centredEnc certC certC_chunk186
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 187: 8 leaves. -/
theorem certC_chunk187_ok :
    checkTree NP.centredEnc certC certC_chunk187
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 188: 7 leaves. -/
theorem certC_chunk188_ok :
    checkTree NP.centredEnc certC certC_chunk188
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 189: 6 leaves. -/
theorem certC_chunk189_ok :
    checkTree NP.centredEnc certC certC_chunk189
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 190: 10 leaves. -/
theorem certC_chunk190_ok :
    checkTree NP.centredEnc certC certC_chunk190
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 191: 1 leaves. -/
theorem certC_chunk191_ok :
    checkTree NP.centredEnc certC certC_chunk191
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 192: 1 leaves. -/
theorem certC_chunk192_ok :
    checkTree NP.centredEnc certC certC_chunk192
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 193: 9 leaves. -/
theorem certC_chunk193_ok :
    checkTree NP.centredEnc certC certC_chunk193
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 194: 8 leaves. -/
theorem certC_chunk194_ok :
    checkTree NP.centredEnc certC certC_chunk194
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part12

open BirkhoffGlobalSection.TangentialHessian.Part12 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk180 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk181 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk182 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk183 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk184 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk185 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk186 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk187 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk188 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk189 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk190 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk191 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk192 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk193 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk194 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) :=
  ⟨certC_chunk180_ok, certC_chunk181_ok, certC_chunk182_ok, certC_chunk183_ok, certC_chunk184_ok, certC_chunk185_ok, certC_chunk186_ok, certC_chunk187_ok, certC_chunk188_ok, certC_chunk189_ok, certC_chunk190_ok, certC_chunk191_ok, certC_chunk192_ok, certC_chunk193_ok, certC_chunk194_ok⟩
