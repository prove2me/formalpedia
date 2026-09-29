-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_00
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:26.874339+00:00
-- url     : https://prove2.me/submissions/d75e33b5-2324-4225-a4a4-fd33f71cf078

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part00

set_option maxRecDepth 100000

/-- Chunk 0: 8 leaves. -/
theorem certC_chunk0_ok :
    checkTree NP.centredEnc certC certC_chunk0
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 1: 8 leaves. -/
theorem certC_chunk1_ok :
    checkTree NP.centredEnc certC certC_chunk1
      (upperHalf (lowerHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 2: 7 leaves. -/
theorem certC_chunk2_ok :
    checkTree NP.centredEnc certC certC_chunk2
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 3: 7 leaves. -/
theorem certC_chunk3_ok :
    checkTree NP.centredEnc certC certC_chunk3
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 4: 1 leaves. -/
theorem certC_chunk4_ok :
    checkTree NP.centredEnc certC certC_chunk4
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 5: 10 leaves. -/
theorem certC_chunk5_ok :
    checkTree NP.centredEnc certC certC_chunk5
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 6: 10 leaves. -/
theorem certC_chunk6_ok :
    checkTree NP.centredEnc certC certC_chunk6
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 7: 8 leaves. -/
theorem certC_chunk7_ok :
    checkTree NP.centredEnc certC certC_chunk7
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 8: 8 leaves. -/
theorem certC_chunk8_ok :
    checkTree NP.centredEnc certC certC_chunk8
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 9: 8 leaves. -/
theorem certC_chunk9_ok :
    checkTree NP.centredEnc certC certC_chunk9
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 10: 9 leaves. -/
theorem certC_chunk10_ok :
    checkTree NP.centredEnc certC certC_chunk10
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 11: 1 leaves. -/
theorem certC_chunk11_ok :
    checkTree NP.centredEnc certC certC_chunk11
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 12: 11 leaves. -/
theorem certC_chunk12_ok :
    checkTree NP.centredEnc certC certC_chunk12
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 13: 9 leaves. -/
theorem certC_chunk13_ok :
    checkTree NP.centredEnc certC certC_chunk13
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 14: 5 leaves. -/
theorem certC_chunk14_ok :
    checkTree NP.centredEnc certC certC_chunk14
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part00

open BirkhoffGlobalSection.TangentialHessian.Part00 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk0 (lowerHalf (lowerHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk1 (upperHalf (lowerHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk2 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk3 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk4 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk5 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk6 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk7 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk8 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk9 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk10 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk11 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk12 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk13 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk14 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) = true) :=
  ⟨certC_chunk0_ok, certC_chunk1_ok, certC_chunk2_ok, certC_chunk3_ok, certC_chunk4_ok, certC_chunk5_ok, certC_chunk6_ok, certC_chunk7_ok, certC_chunk8_ok, certC_chunk9_ok, certC_chunk10_ok, certC_chunk11_ok, certC_chunk12_ok, certC_chunk13_ok, certC_chunk14_ok⟩
