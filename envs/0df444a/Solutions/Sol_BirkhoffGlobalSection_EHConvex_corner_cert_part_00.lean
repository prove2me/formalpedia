-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_00
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:25.418572+00:00
-- url     : https://prove2.me/submissions/da6f32f3-cb6d-4a36-8b5a-97b81cbf7c75

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart00

set_option maxRecDepth 100000

/-- Chunk 0: 1 leaves. -/
theorem cornerK1_chunk0_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk0
      (lowerHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 1: 1 leaves. -/
theorem cornerK1_chunk1_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk1
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 2: 3 leaves. -/
theorem cornerK1_chunk2_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk2
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 3: 1 leaves. -/
theorem cornerK1_chunk3_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk3
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 4: 9 leaves. -/
theorem cornerK1_chunk4_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk4
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 5: 3 leaves. -/
theorem cornerK1_chunk5_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk5
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 6: 1 leaves. -/
theorem cornerK1_chunk6_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk6
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 7: 1 leaves. -/
theorem cornerK1_chunk7_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk7
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 8: 1 leaves. -/
theorem cornerK1_chunk8_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk8
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 9: 10 leaves. -/
theorem cornerK1_chunk9_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk9
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 10: 1 leaves. -/
theorem cornerK1_chunk10_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk10
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 11: 8 leaves. -/
theorem cornerK1_chunk11_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk11
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 12: 1 leaves. -/
theorem cornerK1_chunk12_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk12
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 13: 10 leaves. -/
theorem cornerK1_chunk13_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk13
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 14: 5 leaves. -/
theorem cornerK1_chunk14_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk14
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 15: 5 leaves. -/
theorem cornerK1_chunk15_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk15
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 16: 8 leaves. -/
theorem cornerK1_chunk16_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk16
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 17: 1 leaves. -/
theorem cornerK1_chunk17_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk17
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 18: 1 leaves. -/
theorem cornerK1_chunk18_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk18
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 19: 1 leaves. -/
theorem cornerK1_chunk19_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk19
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 20: 1 leaves. -/
theorem cornerK1_chunk20_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk20
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 21: 10 leaves. -/
theorem cornerK1_chunk21_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk21
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 22: 10 leaves. -/
theorem cornerK1_chunk22_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk22
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 23: 1 leaves. -/
theorem cornerK1_chunk23_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk23
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 24: 7 leaves. -/
theorem cornerK1_chunk24_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk24
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 25: 1 leaves. -/
theorem cornerK1_chunk25_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk25
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 26: 2 leaves. -/
theorem cornerK1_chunk26_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk26
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 27: 1 leaves. -/
theorem cornerK1_chunk27_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk27
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 28: 1 leaves. -/
theorem cornerK1_chunk28_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk28
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 29: 1 leaves. -/
theorem cornerK1_chunk29_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk29
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 30: 1 leaves. -/
theorem cornerK1_chunk30_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk30
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 31: 1 leaves. -/
theorem cornerK1_chunk31_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk31
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 32: 1 leaves. -/
theorem cornerK1_chunk32_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk32
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 33: 1 leaves. -/
theorem cornerK1_chunk33_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk33
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 34: 1 leaves. -/
theorem cornerK1_chunk34_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk34
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 35: 1 leaves. -/
theorem cornerK1_chunk35_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk35
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 36: 10 leaves. -/
theorem cornerK1_chunk36_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk36
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 37: 1 leaves. -/
theorem cornerK1_chunk37_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk37
      (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 38: 10 leaves. -/
theorem cornerK1_chunk38_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk38
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 39: 1 leaves. -/
theorem cornerK1_chunk39_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk39
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 40: 1 leaves. -/
theorem cornerK1_chunk40_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk40
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 41: 1 leaves. -/
theorem cornerK1_chunk41_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk41
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 42: 1 leaves. -/
theorem cornerK1_chunk42_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk42
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 43: 5 leaves. -/
theorem cornerK1_chunk43_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk43
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 44: 8 leaves. -/
theorem cornerK1_chunk44_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk44
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 45: 1 leaves. -/
theorem cornerK1_chunk45_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk45
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 46: 1 leaves. -/
theorem cornerK1_chunk46_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk46
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 47: 10 leaves. -/
theorem cornerK1_chunk47_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk47
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 48: 1 leaves. -/
theorem cornerK1_chunk48_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk48
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 49: 1 leaves. -/
theorem cornerK1_chunk49_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk49
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 50: 10 leaves. -/
theorem cornerK1_chunk50_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk50
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 51: 1 leaves. -/
theorem cornerK1_chunk51_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk51
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 52: 9 leaves. -/
theorem cornerK1_chunk52_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk52
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 53: 10 leaves. -/
theorem cornerK1_chunk53_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk53
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 54: 1 leaves. -/
theorem cornerK1_chunk54_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk54
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 55: 5 leaves. -/
theorem cornerK1_chunk55_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk55
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 56: 1 leaves. -/
theorem cornerK1_chunk56_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk56
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 57: 8 leaves. -/
theorem cornerK1_chunk57_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk57
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 58: 8 leaves. -/
theorem cornerK1_chunk58_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk58
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 59: 5 leaves. -/
theorem cornerK1_chunk59_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk59
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 60: 1 leaves. -/
theorem cornerK1_chunk60_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk60
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 61: 8 leaves. -/
theorem cornerK1_chunk61_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk61
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 62: 1 leaves. -/
theorem cornerK1_chunk62_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk62
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 63: 1 leaves. -/
theorem cornerK1_chunk63_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk63
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 64: 1 leaves. -/
theorem cornerK1_chunk64_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk64
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 65: 1 leaves. -/
theorem cornerK1_chunk65_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk65
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 66: 1 leaves. -/
theorem cornerK1_chunk66_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk66
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 67: 1 leaves. -/
theorem cornerK1_chunk67_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk67
      (lowerHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 68: 1 leaves. -/
theorem cornerK1_chunk68_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk68
      (lowerHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 69: 1 leaves. -/
theorem cornerK1_chunk69_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk69
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 70: 1 leaves. -/
theorem cornerK1_chunk70_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk70
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 71: 1 leaves. -/
theorem cornerK1_chunk71_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk71
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 72: 1 leaves. -/
theorem cornerK1_chunk72_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk72
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 73: 3 leaves. -/
theorem cornerK1_chunk73_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk73
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 74: 9 leaves. -/
theorem cornerK1_chunk74_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk74
      (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 75: 5 leaves. -/
theorem cornerK1_chunk75_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk75
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 76: 6 leaves. -/
theorem cornerK1_chunk76_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk76
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 77: 1 leaves. -/
theorem cornerK1_chunk77_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk77
      (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 78: 1 leaves. -/
theorem cornerK1_chunk78_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk78
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 79: 1 leaves. -/
theorem cornerK1_chunk79_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk79
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 80: 1 leaves. -/
theorem cornerK1_chunk80_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk80
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 81: 1 leaves. -/
theorem cornerK1_chunk81_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk81
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 82: 1 leaves. -/
theorem cornerK1_chunk82_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk82
      (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 83: 1 leaves. -/
theorem cornerK1_chunk83_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk83
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 84: 1 leaves. -/
theorem cornerK1_chunk84_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk84
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 85: 8 leaves. -/
theorem cornerK1_chunk85_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk85
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 86: 1 leaves. -/
theorem cornerK1_chunk86_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk86
      (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 87: 10 leaves. -/
theorem cornerK1_chunk87_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk87
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart00

open BirkhoffGlobalSection.EHConvex.CornerPart00 in
theorem solution :
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk0 (lowerHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk1 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk2 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk3 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk4 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk5 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk6 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk7 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk8 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk9 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk10 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk11 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk12 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk13 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk14 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk15 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk16 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk17 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk18 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk19 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk20 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk21 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk22 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk23 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk24 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk25 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk26 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk27 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk28 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk29 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk30 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk31 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk32 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk33 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk34 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk35 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk36 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk37 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk38 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk39 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk40 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk41 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk42 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk43 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk44 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk45 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk46 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk47 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk48 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk49 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk50 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk51 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk52 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk53 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk54 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk55 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk56 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk57 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk58 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk59 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk60 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk61 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk62 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk63 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk64 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk65 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk66 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk67 (lowerHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk68 (lowerHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk69 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk70 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk71 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk72 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk73 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk74 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk75 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk76 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk77 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk78 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk79 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk80 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk81 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk82 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk83 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk84 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk85 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk86 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk87 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) :=
  ⟨cornerK1_chunk0_ok, cornerK1_chunk1_ok, cornerK1_chunk2_ok, cornerK1_chunk3_ok, cornerK1_chunk4_ok, cornerK1_chunk5_ok, cornerK1_chunk6_ok, cornerK1_chunk7_ok, cornerK1_chunk8_ok, cornerK1_chunk9_ok, cornerK1_chunk10_ok, cornerK1_chunk11_ok, cornerK1_chunk12_ok, cornerK1_chunk13_ok, cornerK1_chunk14_ok, cornerK1_chunk15_ok, cornerK1_chunk16_ok, cornerK1_chunk17_ok, cornerK1_chunk18_ok, cornerK1_chunk19_ok, cornerK1_chunk20_ok, cornerK1_chunk21_ok, cornerK1_chunk22_ok, cornerK1_chunk23_ok, cornerK1_chunk24_ok, cornerK1_chunk25_ok, cornerK1_chunk26_ok, cornerK1_chunk27_ok, cornerK1_chunk28_ok, cornerK1_chunk29_ok, cornerK1_chunk30_ok, cornerK1_chunk31_ok, cornerK1_chunk32_ok, cornerK1_chunk33_ok, cornerK1_chunk34_ok, cornerK1_chunk35_ok, cornerK1_chunk36_ok, cornerK1_chunk37_ok, cornerK1_chunk38_ok, cornerK1_chunk39_ok, cornerK1_chunk40_ok, cornerK1_chunk41_ok, cornerK1_chunk42_ok, cornerK1_chunk43_ok, cornerK1_chunk44_ok, cornerK1_chunk45_ok, cornerK1_chunk46_ok, cornerK1_chunk47_ok, cornerK1_chunk48_ok, cornerK1_chunk49_ok, cornerK1_chunk50_ok, cornerK1_chunk51_ok, cornerK1_chunk52_ok, cornerK1_chunk53_ok, cornerK1_chunk54_ok, cornerK1_chunk55_ok, cornerK1_chunk56_ok, cornerK1_chunk57_ok, cornerK1_chunk58_ok, cornerK1_chunk59_ok, cornerK1_chunk60_ok, cornerK1_chunk61_ok, cornerK1_chunk62_ok, cornerK1_chunk63_ok, cornerK1_chunk64_ok, cornerK1_chunk65_ok, cornerK1_chunk66_ok, cornerK1_chunk67_ok, cornerK1_chunk68_ok, cornerK1_chunk69_ok, cornerK1_chunk70_ok, cornerK1_chunk71_ok, cornerK1_chunk72_ok, cornerK1_chunk73_ok, cornerK1_chunk74_ok, cornerK1_chunk75_ok, cornerK1_chunk76_ok, cornerK1_chunk77_ok, cornerK1_chunk78_ok, cornerK1_chunk79_ok, cornerK1_chunk80_ok, cornerK1_chunk81_ok, cornerK1_chunk82_ok, cornerK1_chunk83_ok, cornerK1_chunk84_ok, cornerK1_chunk85_ok, cornerK1_chunk86_ok, cornerK1_chunk87_ok⟩
