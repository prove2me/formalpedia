-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.certC_part_09
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:38:34.583309+00:00
-- url     : https://prove2.me/submissions/9f71c449-5319-4924-9565-acd1c68693b8

import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.TangentialHessian.Part09

set_option maxRecDepth 100000

/-- Chunk 135: 1 leaves. -/
theorem certC_chunk135_ok :
    checkTree NP.centredEnc certC certC_chunk135
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 136: 11 leaves. -/
theorem certC_chunk136_ok :
    checkTree NP.centredEnc certC certC_chunk136
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 137: 10 leaves. -/
theorem certC_chunk137_ok :
    checkTree NP.centredEnc certC certC_chunk137
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 138: 5 leaves. -/
theorem certC_chunk138_ok :
    checkTree NP.centredEnc certC certC_chunk138
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 139: 8 leaves. -/
theorem certC_chunk139_ok :
    checkTree NP.centredEnc certC certC_chunk139
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 140: 1 leaves. -/
theorem certC_chunk140_ok :
    checkTree NP.centredEnc certC certC_chunk140
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 141: 8 leaves. -/
theorem certC_chunk141_ok :
    checkTree NP.centredEnc certC certC_chunk141
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 142: 9 leaves. -/
theorem certC_chunk142_ok :
    checkTree NP.centredEnc certC certC_chunk142
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 143: 9 leaves. -/
theorem certC_chunk143_ok :
    checkTree NP.centredEnc certC certC_chunk143
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 144: 9 leaves. -/
theorem certC_chunk144_ok :
    checkTree NP.centredEnc certC certC_chunk144
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true := by
  decide +kernel

/-- Chunk 145: 1 leaves. -/
theorem certC_chunk145_ok :
    checkTree NP.centredEnc certC certC_chunk145
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true := by
  decide +kernel

/-- Chunk 146: 9 leaves. -/
theorem certC_chunk146_ok :
    checkTree NP.centredEnc certC certC_chunk146
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 147: 9 leaves. -/
theorem certC_chunk147_ok :
    checkTree NP.centredEnc certC certC_chunk147
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 148: 9 leaves. -/
theorem certC_chunk148_ok :
    checkTree NP.centredEnc certC certC_chunk148
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

/-- Chunk 149: 9 leaves. -/
theorem certC_chunk149_ok :
    checkTree NP.centredEnc certC certC_chunk149
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Part09

open BirkhoffGlobalSection.TangentialHessian.Part09 in
theorem solution :
    (checkTree NP.centredEnc certC certC_chunk135 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk136 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk137 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk138 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk139 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk140 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk141 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk142 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk143 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk144 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk145 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk146 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk147 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk148 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) ∧
    (checkTree NP.centredEnc certC certC_chunk149 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf certC_box 0) 2) 3) 0) 2) 3) 0) 2) 3) 0) 2) = true) :=
  ⟨certC_chunk135_ok, certC_chunk136_ok, certC_chunk137_ok, certC_chunk138_ok, certC_chunk139_ok, certC_chunk140_ok, certC_chunk141_ok, certC_chunk142_ok, certC_chunk143_ok, certC_chunk144_ok, certC_chunk145_ok, certC_chunk146_ok, certC_chunk147_ok, certC_chunk148_ok, certC_chunk149_ok⟩
