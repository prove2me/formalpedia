-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_01
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:39:26.527255+00:00
-- url     : https://prove2.me/submissions/fb03986c-88ca-44c1-a74b-47006f166f13

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart01

set_option maxRecDepth 100000

/-- Chunk 88: 10 leaves. -/
theorem cornerK1_chunk88_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk88
      (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 89: 8 leaves. -/
theorem cornerK1_chunk89_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk89
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 90: 1 leaves. -/
theorem cornerK1_chunk90_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk90
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 91: 1 leaves. -/
theorem cornerK1_chunk91_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk91
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 92: 10 leaves. -/
theorem cornerK1_chunk92_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk92
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 93: 10 leaves. -/
theorem cornerK1_chunk93_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk93
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 94: 1 leaves. -/
theorem cornerK1_chunk94_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk94
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 95: 6 leaves. -/
theorem cornerK1_chunk95_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk95
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 96: 9 leaves. -/
theorem cornerK1_chunk96_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk96
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 97: 8 leaves. -/
theorem cornerK1_chunk97_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk97
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 98: 1 leaves. -/
theorem cornerK1_chunk98_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk98
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 99: 1 leaves. -/
theorem cornerK1_chunk99_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk99
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 100: 10 leaves. -/
theorem cornerK1_chunk100_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk100
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 101: 1 leaves. -/
theorem cornerK1_chunk101_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk101
      (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 102: 1 leaves. -/
theorem cornerK1_chunk102_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk102
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 103: 1 leaves. -/
theorem cornerK1_chunk103_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk103
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 104: 5 leaves. -/
theorem cornerK1_chunk104_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk104
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 105: 10 leaves. -/
theorem cornerK1_chunk105_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk105
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 106: 1 leaves. -/
theorem cornerK1_chunk106_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk106
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 107: 9 leaves. -/
theorem cornerK1_chunk107_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk107
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 108: 1 leaves. -/
theorem cornerK1_chunk108_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk108
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 109: 1 leaves. -/
theorem cornerK1_chunk109_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk109
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 110: 1 leaves. -/
theorem cornerK1_chunk110_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk110
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 111: 1 leaves. -/
theorem cornerK1_chunk111_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk111
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 112: 1 leaves. -/
theorem cornerK1_chunk112_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk112
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 113: 8 leaves. -/
theorem cornerK1_chunk113_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk113
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 114: 1 leaves. -/
theorem cornerK1_chunk114_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk114
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 115: 1 leaves. -/
theorem cornerK1_chunk115_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk115
      (lowerHalf (upperHalf cornerK1_box 0) 1) = true := by
  decide +kernel

/-- Chunk 116: 1 leaves. -/
theorem cornerK1_chunk116_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk116
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 117: 1 leaves. -/
theorem cornerK1_chunk117_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk117
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 118: 1 leaves. -/
theorem cornerK1_chunk118_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk118
      (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 119: 1 leaves. -/
theorem cornerK1_chunk119_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk119
      (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 120: 10 leaves. -/
theorem cornerK1_chunk120_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk120
      (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 121: 1 leaves. -/
theorem cornerK1_chunk121_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk121
      (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 122: 6 leaves. -/
theorem cornerK1_chunk122_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk122
      (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 123: 10 leaves. -/
theorem cornerK1_chunk123_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk123
      (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 124: 6 leaves. -/
theorem cornerK1_chunk124_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk124
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 125: 9 leaves. -/
theorem cornerK1_chunk125_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk125
      (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 126: 6 leaves. -/
theorem cornerK1_chunk126_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk126
      (upperHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 127: 1 leaves. -/
theorem cornerK1_chunk127_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk127
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 128: 1 leaves. -/
theorem cornerK1_chunk128_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk128
      (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 129: 1 leaves. -/
theorem cornerK1_chunk129_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk129
      (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 130: 6 leaves. -/
theorem cornerK1_chunk130_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk130
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 131: 5 leaves. -/
theorem cornerK1_chunk131_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk131
      (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 132: 1 leaves. -/
theorem cornerK1_chunk132_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk132
      (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 133: 1 leaves. -/
theorem cornerK1_chunk133_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk133
      (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 134: 1 leaves. -/
theorem cornerK1_chunk134_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk134
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 135: 1 leaves. -/
theorem cornerK1_chunk135_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk135
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 136: 1 leaves. -/
theorem cornerK1_chunk136_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk136
      (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 137: 7 leaves. -/
theorem cornerK1_chunk137_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk137
      (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 138: 6 leaves. -/
theorem cornerK1_chunk138_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk138
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 139: 1 leaves. -/
theorem cornerK1_chunk139_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk139
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 140: 2 leaves. -/
theorem cornerK1_chunk140_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk140
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 141: 1 leaves. -/
theorem cornerK1_chunk141_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk141
      (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 142: 9 leaves. -/
theorem cornerK1_chunk142_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk142
      (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 143: 1 leaves. -/
theorem cornerK1_chunk143_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk143
      (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 144: 1 leaves. -/
theorem cornerK1_chunk144_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk144
      (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true := by
  decide +kernel

/-- Chunk 145: 1 leaves. -/
theorem cornerK1_chunk145_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk145
      (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true := by
  decide +kernel

/-- Chunk 146: 3 leaves. -/
theorem cornerK1_chunk146_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk146
      (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) = true := by
  decide +kernel

/-- Chunk 147: 1 leaves. -/
theorem cornerK1_chunk147_ok :
    checkTree NP.centredEnc cornerK1 cornerK1_chunk147
      (upperHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart01

open BirkhoffGlobalSection.EHConvex.CornerPart01 in
theorem solution :
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk88 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk89 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk90 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk91 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk92 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk93 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk94 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk95 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk96 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk97 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk98 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk99 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk100 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk101 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk102 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk103 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk104 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk105 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk106 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk107 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk108 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk109 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk110 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk111 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk112 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk113 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk114 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf cornerK1_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk115 (lowerHalf (upperHalf cornerK1_box 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk116 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk117 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk118 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk119 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk120 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk121 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk122 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk123 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk124 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk125 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk126 (upperHalf (lowerHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk127 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk128 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk129 (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk130 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk131 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk132 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk133 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk134 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk135 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk136 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk137 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk138 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk139 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk140 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk141 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk142 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk143 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk144 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) 0) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk145 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) 2) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk146 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) 1) = true) ∧
    (checkTree NP.centredEnc cornerK1 cornerK1_chunk147 (upperHalf (upperHalf (upperHalf (upperHalf cornerK1_box 0) 1) 2) 0) = true) :=
  ⟨cornerK1_chunk88_ok, cornerK1_chunk89_ok, cornerK1_chunk90_ok, cornerK1_chunk91_ok, cornerK1_chunk92_ok, cornerK1_chunk93_ok, cornerK1_chunk94_ok, cornerK1_chunk95_ok, cornerK1_chunk96_ok, cornerK1_chunk97_ok, cornerK1_chunk98_ok, cornerK1_chunk99_ok, cornerK1_chunk100_ok, cornerK1_chunk101_ok, cornerK1_chunk102_ok, cornerK1_chunk103_ok, cornerK1_chunk104_ok, cornerK1_chunk105_ok, cornerK1_chunk106_ok, cornerK1_chunk107_ok, cornerK1_chunk108_ok, cornerK1_chunk109_ok, cornerK1_chunk110_ok, cornerK1_chunk111_ok, cornerK1_chunk112_ok, cornerK1_chunk113_ok, cornerK1_chunk114_ok, cornerK1_chunk115_ok, cornerK1_chunk116_ok, cornerK1_chunk117_ok, cornerK1_chunk118_ok, cornerK1_chunk119_ok, cornerK1_chunk120_ok, cornerK1_chunk121_ok, cornerK1_chunk122_ok, cornerK1_chunk123_ok, cornerK1_chunk124_ok, cornerK1_chunk125_ok, cornerK1_chunk126_ok, cornerK1_chunk127_ok, cornerK1_chunk128_ok, cornerK1_chunk129_ok, cornerK1_chunk130_ok, cornerK1_chunk131_ok, cornerK1_chunk132_ok, cornerK1_chunk133_ok, cornerK1_chunk134_ok, cornerK1_chunk135_ok, cornerK1_chunk136_ok, cornerK1_chunk137_ok, cornerK1_chunk138_ok, cornerK1_chunk139_ok, cornerK1_chunk140_ok, cornerK1_chunk141_ok, cornerK1_chunk142_ok, cornerK1_chunk143_ok, cornerK1_chunk144_ok, cornerK1_chunk145_ok, cornerK1_chunk146_ok, cornerK1_chunk147_ok⟩
