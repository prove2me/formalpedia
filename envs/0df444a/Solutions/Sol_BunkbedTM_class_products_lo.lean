-- Prove2me | solution 1 for BunkbedTM.class_products_lo
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T16:53:17.871168+00:00
-- url     : https://prove2.me/submissions/1ba51ac6-7e39-4c1d-8103-d0ff5fef7b16

import Definitions.Def_BunkbedTransferPartial

/-!
# The first eight class products

`Σ_{k < 8} ck k * wk k = wzDlo`, checked one power of `z` at a time: grading both sides by `z`
turns one four-variable polynomial identity into thirteen three-variable ones, which is the
difference between 115 s and 55 s of `ring`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

open Bunkbed Bunkbed.Hyper Bunkbed.TM Finset

namespace BunkbedTMGradedLo

private def cg0_0_p0 (x y u : Rat) : Rat := 10 * u ^ 6 + 19 * y * u ^ 5 + 11 * y ^ 2 * u ^ 4 + 2 * y ^ 3 * u ^ 3 + 39 * x * u ^ 5 + 78 * x * y * u ^ 4 + 49 * x * y ^ 2 * u ^ 3 + 12 * x * y ^ 3 * u ^ 2 + x * y ^ 4 * u + 53 * x ^ 2 * u ^ 4 + 103 * x ^ 2 * y * u ^ 3 + 59 * x ^ 2 * y ^ 2 * u ^ 2 + 13 * x ^ 2 * y ^ 3 * u + x ^ 2 * y ^ 4
private def cg0_0_p1 (x y u : Rat) : Rat := 32 * x ^ 3 * u ^ 3 + 56 * x ^ 3 * y * u ^ 2 + 24 * x ^ 3 * y ^ 2 * u + 3 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 13 * x ^ 4 * y * u + 3 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg0_0 (x y u : Rat) : Rat := cg0_0_p0 x y u + cg0_0_p1 x y u
private def cg0_1_p0 (x y u : Rat) : Rat := 23 * u ^ 5 + 37 * y * u ^ 4 + 20 * y ^ 2 * u ^ 3 + 6 * y ^ 3 * u ^ 2 + y ^ 4 * u + 79 * x * u ^ 4 + 125 * x * y * u ^ 3 + 59 * x * y ^ 2 * u ^ 2 + 12 * x * y ^ 3 * u + x * y ^ 4 + 88 * x ^ 2 * u ^ 3 + 127 * x ^ 2 * y * u ^ 2 + 48 * x ^ 2 * y ^ 2 * u + 6 * x ^ 2 * y ^ 3
private def cg0_1_p1 (x y u : Rat) : Rat := 38 * x ^ 3 * u ^ 2 + 43 * x ^ 3 * y * u + 9 * x ^ 3 * y ^ 2 + 6 * x ^ 4 * u + 4 * x ^ 4 * y
private def cg0_1 (x y u : Rat) : Rat := cg0_1_p0 x y u + cg0_1_p1 x y u
private def cg0_2 (x y u : Rat) : Rat := 27 * u ^ 4 + 33 * y * u ^ 3 + 17 * y ^ 2 * u ^ 2 + 4 * y ^ 3 * u + 71 * x * u ^ 3 + 78 * x * y * u ^ 2 + 28 * x * y ^ 2 * u + 4 * x * y ^ 3 + 52 * x ^ 2 * u ^ 2 + 51 * x ^ 2 * y * u + 11 * x ^ 2 * y ^ 2 + 10 * x ^ 3 * u + 6 * x ^ 3 * y - x ^ 4
private def cg0_3 (x y u : Rat) : Rat := 13 * u ^ 3 + 14 * y * u ^ 2 + 6 * y ^ 2 * u + 23 * x * u ^ 2 + 20 * x * y * u + 6 * x * y ^ 2 + 6 * x ^ 2 * u + 6 * x ^ 2 * y - 4 * x ^ 3
private def cg0_4 (x y u : Rat) : Rat := u ^ 2 + 4 * y * u + 3 * x * u + 4 * x * y - 6 * x ^ 2
private def cg0_5 (x y u : Rat) : Rat := 2 * u - 4 * x
private def cg0_6 (x y u : Rat) : Rat := -1
private def cg1_0_p0 (x y u : Rat) : Rat := -4 * u ^ 6 - 4 * y * u ^ 5 - y ^ 2 * u ^ 4 - 34 * x * u ^ 5 - 41 * x * y * u ^ 4 - 16 * x * y ^ 2 * u ^ 3 - 2 * x * y ^ 3 * u ^ 2 - 80 * x ^ 2 * u ^ 4 - 92 * x ^ 2 * y * u ^ 3 - 34 * x ^ 2 * y ^ 2 * u ^ 2 - 4 * x ^ 2 * y ^ 3 * u - 82 * x ^ 3 * u ^ 3 - 81 * x ^ 3 * y * u ^ 2 - 24 * x ^ 3 * y ^ 2 * u
private def cg1_0_p1 (x y u : Rat) : Rat := -2 * x ^ 3 * y ^ 3 - 41 * x ^ 4 * u ^ 2 - 30 * x ^ 4 * y * u - 5 * x ^ 4 * y ^ 2 - 10 * x ^ 5 * u - 4 * x ^ 5 * y - x ^ 6
private def cg1_0 (x y u : Rat) : Rat := cg1_0_p0 x y u + cg1_0_p1 x y u
private def cg1_1_p0 (x y u : Rat) : Rat := -22 * u ^ 5 - 27 * y * u ^ 4 - 12 * y ^ 2 * u ^ 3 - 2 * y ^ 3 * u ^ 2 - 108 * x * u ^ 4 - 112 * x * y * u ^ 3 - 37 * x * y ^ 2 * u ^ 2 - 4 * x * y ^ 3 * u - 184 * x ^ 2 * u ^ 3 - 160 * x ^ 2 * y * u ^ 2 - 38 * x ^ 2 * y ^ 2 * u - 2 * x ^ 2 * y ^ 3 - 138 * x ^ 3 * u ^ 2 - 92 * x ^ 3 * y * u
private def cg1_1_p1 (x y u : Rat) : Rat := -13 * x ^ 3 * y ^ 2 - 46 * x ^ 4 * u - 17 * x ^ 4 * y - 6 * x ^ 5
private def cg1_1 (x y u : Rat) : Rat := cg1_1_p0 x y u + cg1_1_p1 x y u
private def cg1_2 (x y u : Rat) : Rat := -31 * u ^ 4 - 28 * y * u ^ 3 - 7 * y ^ 2 * u ^ 2 - 118 * x * u ^ 3 - 81 * x * y * u ^ 2 - 14 * x * y ^ 2 * u - 155 * x ^ 2 * u ^ 2 - 78 * x ^ 2 * y * u - 7 * x ^ 2 * y ^ 2 - 80 * x ^ 3 * u - 25 * x ^ 3 * y - 15 * x ^ 4
private def cg1_3 (x y u : Rat) : Rat := -20 * u ^ 3 - 10 * y * u ^ 2 - 60 * x * u ^ 2 - 20 * x * y * u - 60 * x ^ 2 * u - 10 * x ^ 2 * y - 20 * x ^ 3
private def cg1_4 (x y u : Rat) : Rat := -7 * u ^ 2 - 14 * x * u - 15 * x ^ 2
private def cg1_5 (x y u : Rat) : Rat := -6 * x
private def cg1_6 (x y u : Rat) : Rat := -1
private def cg2_0_p0 (x y u : Rat) : Rat := -16 * u ^ 6 - 32 * y * u ^ 5 - 24 * y ^ 2 * u ^ 4 - 8 * y ^ 3 * u ^ 3 - y ^ 4 * u ^ 2 - 64 * x * u ^ 5 - 112 * x * y * u ^ 4 - 72 * x * y ^ 2 * u ^ 3 - 20 * x * y ^ 3 * u ^ 2 - 2 * x * y ^ 4 * u - 104 * x ^ 2 * u ^ 4 - 152 * x ^ 2 * y * u ^ 3 - 78 * x ^ 2 * y ^ 2 * u ^ 2 - 16 * x ^ 2 * y ^ 3 * u
private def cg2_0_p1 (x y u : Rat) : Rat := -x ^ 2 * y ^ 4 - 88 * x ^ 3 * u ^ 3 - 100 * x ^ 3 * y * u ^ 2 - 36 * x ^ 3 * y ^ 2 * u - 4 * x ^ 3 * y ^ 3 - 41 * x ^ 4 * u ^ 2 - 32 * x ^ 4 * y * u - 6 * x ^ 4 * y ^ 2 - 10 * x ^ 5 * u - 4 * x ^ 5 * y - x ^ 6
private def cg2_0 (x y u : Rat) : Rat := cg2_0_p0 x y u + cg2_0_p1 x y u
private def cg2_1_p0 (x y u : Rat) : Rat := -48 * u ^ 5 - 72 * y * u ^ 4 - 36 * y ^ 2 * u ^ 3 - 6 * y ^ 3 * u ^ 2 - 168 * x * u ^ 4 - 216 * x * y * u ^ 3 - 90 * x * y ^ 2 * u ^ 2 - 12 * x * y ^ 3 * u - 228 * x ^ 2 * u ^ 3 - 234 * x ^ 2 * y * u ^ 2 - 72 * x ^ 2 * y ^ 2 * u - 6 * x ^ 2 * y ^ 3 - 150 * x ^ 3 * u ^ 2 - 108 * x ^ 3 * y * u
private def cg2_1_p1 (x y u : Rat) : Rat := -18 * x ^ 3 * y ^ 2 - 48 * x ^ 4 * u - 18 * x ^ 4 * y - 6 * x ^ 5
private def cg2_1 (x y u : Rat) : Rat := cg2_1_p0 x y u + cg2_1_p1 x y u
private def cg2_2 (x y u : Rat) : Rat := -60 * u ^ 4 - 60 * y * u ^ 3 - 15 * y ^ 2 * u ^ 2 - 180 * x * u ^ 3 - 150 * x * y * u ^ 2 - 30 * x * y ^ 2 * u - 195 * x ^ 2 * u ^ 2 - 120 * x ^ 2 * y * u - 15 * x ^ 2 * y ^ 2 - 90 * x ^ 3 * u - 30 * x ^ 3 * y - 15 * x ^ 4
private def cg2_3 (x y u : Rat) : Rat := -40 * u ^ 3 - 20 * y * u ^ 2 - 100 * x * u ^ 2 - 40 * x * y * u - 80 * x ^ 2 * u - 20 * x ^ 2 * y - 20 * x ^ 3
private def cg2_4 (x y u : Rat) : Rat := -15 * u ^ 2 - 30 * x * u - 15 * x ^ 2
private def cg2_5 (x y u : Rat) : Rat := -6 * x
private def cg2_6 (x y u : Rat) : Rat := -1
private def cg3_0_p0 (x y u : Rat) : Rat := 16 * u ^ 6 + 48 * y * u ^ 5 + 56 * y ^ 2 * u ^ 4 + 32 * y ^ 3 * u ^ 3 + 9 * y ^ 4 * u ^ 2 + y ^ 5 * u + 48 * x * u ^ 5 + 128 * x * y * u ^ 4 + 128 * x * y ^ 2 * u ^ 3 + 60 * x * y ^ 3 * u ^ 2 + 13 * x * y ^ 4 * u + x * y ^ 5 + 56 * x ^ 2 * u ^ 4 + 128 * x ^ 2 * y * u ^ 3
private def cg3_0_p1 (x y u : Rat) : Rat := 102 * x ^ 2 * y ^ 2 * u ^ 2 + 34 * x ^ 2 * y ^ 3 * u + 4 * x ^ 2 * y ^ 4 + 32 * x ^ 3 * u ^ 3 + 60 * x ^ 3 * y * u ^ 2 + 34 * x ^ 3 * y ^ 2 * u + 6 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 13 * x ^ 4 * y * u + 4 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg3_0 (x y u : Rat) : Rat := cg3_0_p0 x y u + cg3_0_p1 x y u
private def cg3_1_p0 (x y u : Rat) : Rat := 48 * u ^ 5 + 120 * y * u ^ 4 + 108 * y ^ 2 * u ^ 3 + 42 * y ^ 3 * u ^ 2 + 6 * y ^ 4 * u + 120 * x * u ^ 4 + 264 * x * y * u ^ 3 + 198 * x * y ^ 2 * u ^ 2 + 60 * x * y ^ 3 * u + 6 * x * y ^ 4 + 108 * x ^ 2 * u ^ 3 + 198 * x ^ 2 * y * u ^ 2 + 108 * x ^ 2 * y ^ 2 * u + 18 * x ^ 2 * y ^ 3
private def cg3_1_p1 (x y u : Rat) : Rat := 42 * x ^ 3 * u ^ 2 + 60 * x ^ 3 * y * u + 18 * x ^ 3 * y ^ 2 + 6 * x ^ 4 * u + 6 * x ^ 4 * y
private def cg3_1 (x y u : Rat) : Rat := cg3_1_p0 x y u + cg3_1_p1 x y u
private def cg3_2 (x y u : Rat) : Rat := 60 * u ^ 4 + 120 * y * u ^ 3 + 75 * y ^ 2 * u ^ 2 + 15 * y ^ 3 * u + 120 * x * u ^ 3 + 210 * x * y * u ^ 2 + 105 * x * y ^ 2 * u + 15 * x * y ^ 3 + 75 * x ^ 2 * u ^ 2 + 105 * x ^ 2 * y * u + 30 * x ^ 2 * y ^ 2 + 15 * x ^ 3 * u + 15 * x ^ 3 * y
private def cg3_3 (x y u : Rat) : Rat := 40 * u ^ 3 + 60 * y * u ^ 2 + 20 * y ^ 2 * u + 60 * x * u ^ 2 + 80 * x * y * u + 20 * x * y ^ 2 + 20 * x ^ 2 * u + 20 * x ^ 2 * y
private def cg3_4 (x y u : Rat) : Rat := 15 * u ^ 2 + 15 * y * u + 15 * x * u + 15 * x * y
private def cg3_5 (x y u : Rat) : Rat := 6 * u
private def cg3_6 (x y u : Rat) : Rat := -1
private def cg4_0_p0 (x y u : Rat) : Rat := 28 * u ^ 6 + 76 * y * u ^ 5 + 79 * y ^ 2 * u ^ 4 + 40 * y ^ 3 * u ^ 3 + 10 * y ^ 4 * u ^ 2 + y ^ 5 * u + 78 * x * u ^ 5 + 199 * x * y * u ^ 4 + 184 * x * y ^ 2 * u ^ 3 + 78 * x * y ^ 3 * u ^ 2 + 15 * x * y ^ 4 * u + x * y ^ 5 + 80 * x ^ 2 * u ^ 4 + 188 * x ^ 2 * y * u ^ 3
private def cg4_0_p1 (x y u : Rat) : Rat := 146 * x ^ 2 * y ^ 2 * u ^ 2 + 46 * x ^ 2 * y ^ 3 * u + 5 * x ^ 2 * y ^ 4 + 38 * x ^ 3 * u ^ 3 + 79 * x ^ 3 * y * u ^ 2 + 46 * x ^ 3 * y ^ 2 * u + 8 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 15 * x ^ 4 * y * u + 5 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg4_0 (x y u : Rat) : Rat := cg4_0_p0 x y u + cg4_0_p1 x y u
private def cg4_1_p0 (x y u : Rat) : Rat := 62 * u ^ 5 + 137 * y * u ^ 4 + 109 * y ^ 2 * u ^ 3 + 38 * y ^ 3 * u ^ 2 + 5 * y ^ 4 * u + 154 * x * u ^ 4 + 313 * x * y * u ^ 3 + 212 * x * y ^ 2 * u ^ 2 + 57 * x * y ^ 3 * u + 5 * x * y ^ 4 + 134 * x ^ 2 * u ^ 3 + 239 * x ^ 2 * y * u ^ 2 + 124 * x ^ 2 * y ^ 2 * u + 19 * x ^ 2 * y ^ 3
private def cg4_1_p1 (x y u : Rat) : Rat := 50 * x ^ 3 * u ^ 2 + 70 * x ^ 3 * y * u + 21 * x ^ 3 * y ^ 2 + 8 * x ^ 4 * u + 7 * x ^ 4 * y
private def cg4_1 (x y u : Rat) : Rat := cg4_1_p0 x y u + cg4_1_p1 x y u
private def cg4_2 (x y u : Rat) : Rat := 63 * u ^ 4 + 107 * y * u ^ 3 + 59 * y ^ 2 * u ^ 2 + 11 * y ^ 3 * u + 136 * x * u ^ 3 + 208 * x * y * u ^ 2 + 89 * x * y ^ 2 * u + 11 * x * y ^ 3 + 93 * x ^ 2 * u ^ 2 + 120 * x ^ 2 * y * u + 30 * x ^ 2 * y ^ 2 + 23 * x ^ 3 * u + 19 * x ^ 3 * y
private def cg4_3 (x y u : Rat) : Rat := 39 * u ^ 3 + 46 * y * u ^ 2 + 14 * y ^ 2 * u + 73 * x * u ^ 2 + 70 * x * y * u + 14 * x * y ^ 2 + 34 * x ^ 2 * u + 24 * x ^ 2 * y
private def cg4_4 (x y u : Rat) : Rat := 15 * u ^ 2 + 11 * y * u + 22 * x * u + 11 * x * y - x ^ 2
private def cg4_5 (x y u : Rat) : Rat := 4 * u - 2 * x
private def cg4_6 (x y u : Rat) : Rat := -1
private def cg5_0_p0 (x y u : Rat) : Rat := 10 * u ^ 6 + 13 * y * u ^ 5 - 4 * y ^ 3 * u ^ 3 - y ^ 4 * u ^ 2 + 37 * x * u ^ 5 + 53 * x * y * u ^ 4 + 9 * x * y ^ 2 * u ^ 3 - 8 * x * y ^ 3 * u ^ 2 - 2 * x * y ^ 4 * u + 51 * x ^ 2 * u ^ 4 + 78 * x ^ 2 * y * u ^ 3 + 21 * x ^ 2 * y ^ 2 * u ^ 2 - 4 * x ^ 2 * y ^ 3 * u - x ^ 2 * y ^ 4
private def cg5_0_p1 (x y u : Rat) : Rat := 32 * x ^ 3 * u ^ 3 + 50 * x ^ 3 * y * u ^ 2 + 15 * x ^ 3 * y ^ 2 * u + 9 * x ^ 4 * u ^ 2 + 13 * x ^ 4 * y * u + 3 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg5_0 (x y u : Rat) : Rat := cg5_0_p0 x y u + cg5_0_p1 x y u
private def cg5_1_p0 (x y u : Rat) : Rat := 12 * u ^ 5 - 2 * y * u ^ 4 - 15 * y ^ 2 * u ^ 3 - 5 * y ^ 3 * u ^ 2 + 52 * x * u ^ 4 + 30 * x * y * u ^ 3 - 19 * x * y ^ 2 * u ^ 2 - 8 * x * y ^ 3 * u + 66 * x ^ 2 * u ^ 3 + 58 * x ^ 2 * y * u ^ 2 - x ^ 2 * y ^ 2 * u - 3 * x ^ 2 * y ^ 3 + 32 * x ^ 3 * u ^ 2 + 30 * x ^ 3 * y * u
private def cg5_1_p1 (x y u : Rat) : Rat := 3 * x ^ 3 * y ^ 2 + 6 * x ^ 4 * u + 4 * x ^ 4 * y
private def cg5_1 (x y u : Rat) : Rat := cg5_1_p0 x y u + cg5_1_p1 x y u
private def cg5_2 (x y u : Rat) : Rat := 4 * u ^ 4 - 8 * y * u ^ 3 - 4 * y ^ 2 * u ^ 2 + y ^ 3 * u + 23 * x * u ^ 3 + x * y * u ^ 2 - 5 * x * y ^ 2 * u + x * y ^ 3 + 25 * x ^ 2 * u ^ 2 + 13 * x ^ 2 * y * u - x ^ 2 * y ^ 2 + 8 * x ^ 3 * u + 4 * x ^ 3 * y - x ^ 4
private def cg5_3 (x y u : Rat) : Rat := -u ^ 3 + 3 * y ^ 2 * u + 7 * x * u ^ 2 + 3 * x * y * u + 3 * x * y ^ 2 + 4 * x ^ 2 * u + 3 * x ^ 2 * y - 4 * x ^ 3
private def cg5_4 (x y u : Rat) : Rat := u ^ 2 + 4 * y * u + 3 * x * u + 4 * x * y - 6 * x ^ 2
private def cg5_5 (x y u : Rat) : Rat := 2 * u - 4 * x
private def cg5_6 (x y u : Rat) : Rat := -1
private def cg6_0_p0 (x y u : Rat) : Rat := -16 * u ^ 6 - 32 * y * u ^ 5 - 24 * y ^ 2 * u ^ 4 - 8 * y ^ 3 * u ^ 3 - y ^ 4 * u ^ 2 - 64 * x * u ^ 5 - 112 * x * y * u ^ 4 - 72 * x * y ^ 2 * u ^ 3 - 20 * x * y ^ 3 * u ^ 2 - 2 * x * y ^ 4 * u - 104 * x ^ 2 * u ^ 4 - 152 * x ^ 2 * y * u ^ 3 - 78 * x ^ 2 * y ^ 2 * u ^ 2 - 16 * x ^ 2 * y ^ 3 * u
private def cg6_0_p1 (x y u : Rat) : Rat := -x ^ 2 * y ^ 4 - 88 * x ^ 3 * u ^ 3 - 100 * x ^ 3 * y * u ^ 2 - 36 * x ^ 3 * y ^ 2 * u - 4 * x ^ 3 * y ^ 3 - 41 * x ^ 4 * u ^ 2 - 32 * x ^ 4 * y * u - 6 * x ^ 4 * y ^ 2 - 10 * x ^ 5 * u - 4 * x ^ 5 * y - x ^ 6
private def cg6_0 (x y u : Rat) : Rat := cg6_0_p0 x y u + cg6_0_p1 x y u
private def cg6_1_p0 (x y u : Rat) : Rat := -44 * u ^ 5 - 62 * y * u ^ 4 - 30 * y ^ 2 * u ^ 3 - 5 * y ^ 3 * u ^ 2 - 160 * x * u ^ 4 - 192 * x * y * u ^ 3 - 76 * x * y ^ 2 * u ^ 2 - 10 * x * y ^ 3 * u - 224 * x ^ 2 * u ^ 3 - 216 * x ^ 2 * y * u ^ 2 - 62 * x ^ 2 * y ^ 2 * u - 5 * x ^ 2 * y ^ 3 - 150 * x ^ 3 * u ^ 2 - 104 * x ^ 3 * y * u
private def cg6_1_p1 (x y u : Rat) : Rat := -16 * x ^ 3 * y ^ 2 - 48 * x ^ 4 * u - 18 * x ^ 4 * y - 6 * x ^ 5
private def cg6_1 (x y u : Rat) : Rat := cg6_1_p0 x y u + cg6_1_p1 x y u
private def cg6_2 (x y u : Rat) : Rat := -44 * u ^ 4 - 40 * y * u ^ 3 - 10 * y ^ 2 * u ^ 2 - 150 * x * u ^ 3 - 107 * x * y * u ^ 2 - 20 * x * y ^ 2 * u - 180 * x ^ 2 * u ^ 2 - 94 * x ^ 2 * y * u - 10 * x ^ 2 * y ^ 2 - 86 * x ^ 3 * u - 27 * x ^ 3 * y - 15 * x ^ 4
private def cg6_3 (x y u : Rat) : Rat := -24 * u ^ 3 - 12 * y * u ^ 2 - 68 * x * u ^ 2 - 24 * x * y * u - 64 * x ^ 2 * u - 12 * x ^ 2 * y - 20 * x ^ 3
private def cg6_4 (x y u : Rat) : Rat := -7 * u ^ 2 - 14 * x * u - 15 * x ^ 2
private def cg6_5 (x y u : Rat) : Rat := -6 * x
private def cg6_6 (x y u : Rat) : Rat := -1
private def cg7_0_p0 (x y u : Rat) : Rat := 16 * u ^ 6 + 48 * y * u ^ 5 + 56 * y ^ 2 * u ^ 4 + 32 * y ^ 3 * u ^ 3 + 9 * y ^ 4 * u ^ 2 + y ^ 5 * u + 48 * x * u ^ 5 + 128 * x * y * u ^ 4 + 128 * x * y ^ 2 * u ^ 3 + 60 * x * y ^ 3 * u ^ 2 + 13 * x * y ^ 4 * u + x * y ^ 5 + 56 * x ^ 2 * u ^ 4 + 128 * x ^ 2 * y * u ^ 3
private def cg7_0_p1 (x y u : Rat) : Rat := 102 * x ^ 2 * y ^ 2 * u ^ 2 + 34 * x ^ 2 * y ^ 3 * u + 4 * x ^ 2 * y ^ 4 + 32 * x ^ 3 * u ^ 3 + 60 * x ^ 3 * y * u ^ 2 + 34 * x ^ 3 * y ^ 2 * u + 6 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 13 * x ^ 4 * y * u + 4 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg7_0 (x y u : Rat) : Rat := cg7_0_p0 x y u + cg7_0_p1 x y u
private def cg7_1_p0 (x y u : Rat) : Rat := 52 * u ^ 5 + 130 * y * u ^ 4 + 114 * y ^ 2 * u ^ 3 + 43 * y ^ 3 * u ^ 2 + 6 * y ^ 4 * u + 128 * x * u ^ 4 + 288 * x * y * u ^ 3 + 212 * x * y ^ 2 * u ^ 2 + 62 * x * y ^ 3 * u + 6 * x * y ^ 4 + 112 * x ^ 2 * u ^ 3 + 216 * x ^ 2 * y * u ^ 2 + 118 * x ^ 2 * y ^ 2 * u + 19 * x ^ 2 * y ^ 3
private def cg7_1_p1 (x y u : Rat) : Rat := 42 * x ^ 3 * u ^ 2 + 64 * x ^ 3 * y * u + 20 * x ^ 3 * y ^ 2 + 6 * x ^ 4 * u + 6 * x ^ 4 * y
private def cg7_1 (x y u : Rat) : Rat := cg7_1_p0 x y u + cg7_1_p1 x y u
private def cg7_2 (x y u : Rat) : Rat := 72 * u ^ 4 + 130 * y * u ^ 3 + 74 * y ^ 2 * u ^ 2 + 14 * y ^ 3 * u + 146 * x * u ^ 3 + 239 * x * y * u ^ 2 + 107 * x * y ^ 2 * u + 14 * x * y ^ 3 + 90 * x ^ 2 * u ^ 2 + 127 * x ^ 2 * y * u + 33 * x ^ 2 * y ^ 2 + 19 * x ^ 3 * u + 18 * x ^ 3 * y
private def cg7_3 (x y u : Rat) : Rat := 46 * u ^ 3 + 56 * y * u ^ 2 + 17 * y ^ 2 * u + 78 * x * u ^ 2 + 80 * x * y * u + 17 * x * y ^ 2 + 32 * x ^ 2 * u + 24 * x ^ 2 * y
private def cg7_4 (x y u : Rat) : Rat := 15 * u ^ 2 + 11 * y * u + 22 * x * u + 11 * x * y - x ^ 2
private def cg7_5 (x y u : Rat) : Rat := 4 * u - 2 * x
private def cg7_6 (x y u : Rat) : Rat := -1
private def dg0_0_p0 (x y u : Rat) : Rat := 10 * u ^ 6 + 21 * y * u ^ 5 + 12 * y ^ 2 * u ^ 4 + 2 * y ^ 3 * u ^ 3 + 30 * x * u ^ 5 + 69 * x * y * u ^ 4 + 39 * x * y ^ 2 * u ^ 3 + 6 * x * y ^ 3 * u ^ 2 + 26 * x ^ 2 * u ^ 4 + 71 * x ^ 2 * y * u ^ 3 + 39 * x ^ 2 * y ^ 2 * u ^ 2 + 5 * x ^ 2 * y ^ 3 * u + 6 * x ^ 3 * u ^ 3 + 25 * x ^ 3 * y * u ^ 2
private def dg0_0_p1 (x y u : Rat) : Rat := 13 * x ^ 3 * y ^ 2 * u + x ^ 3 * y ^ 3 + 2 * x ^ 4 * y * u + x ^ 4 * y ^ 2
private def dg0_0 (x y u : Rat) : Rat := dg0_0_p0 x y u + dg0_0_p1 x y u
private def dg0_1 (x y u : Rat) : Rat := 24 * u ^ 5 + 28 * y * u ^ 4 + 7 * y ^ 2 * u ^ 3 + 74 * x * u ^ 4 + 89 * x * y * u ^ 3 + 21 * x * y ^ 2 * u ^ 2 + 66 * x ^ 2 * u ^ 3 + 83 * x ^ 2 * y * u ^ 2 + 17 * x ^ 2 * y ^ 2 * u + 18 * x ^ 3 * u ^ 2 + 23 * x ^ 3 * y * u + 3 * x ^ 3 * y ^ 2 + 2 * x ^ 4 * u + x ^ 4 * y
private def dg0_2 (x y u : Rat) : Rat := 16 * u ^ 4 + 8 * y * u ^ 3 + 49 * x * u ^ 3 + 24 * x * y * u ^ 2 + 41 * x ^ 2 * u ^ 2 + 19 * x ^ 2 * y * u + 8 * x ^ 3 * u + 3 * x ^ 3 * y
private def dg0_3 (x y u : Rat) : Rat := 4 * u ^ 3 + 12 * x * u ^ 2 + 8 * x ^ 2 * u
private def dg1_0_p0 (x y u : Rat) : Rat := 7 * u ^ 6 + 27 * y * u ^ 5 + 32 * y ^ 2 * u ^ 4 + 14 * y ^ 3 * u ^ 3 + 2 * y ^ 4 * u ^ 2 + 10 * x * u ^ 5 + 52 * x * y * u ^ 4 + 71 * x * y ^ 2 * u ^ 3 + 31 * x * y ^ 3 * u ^ 2 + 4 * x * y ^ 4 * u + 3 * x ^ 2 * u ^ 4 + 29 * x ^ 2 * y * u ^ 3 + 51 * x ^ 2 * y ^ 2 * u ^ 2 + 21 * x ^ 2 * y ^ 3 * u
private def dg1_0_p1 (x y u : Rat) : Rat := 2 * x ^ 2 * y ^ 4 + 4 * x ^ 3 * y * u ^ 2 + 13 * x ^ 3 * y ^ 2 * u + 4 * x ^ 3 * y ^ 3 + x ^ 4 * y ^ 2
private def dg1_0 (x y u : Rat) : Rat := dg1_0_p0 x y u + dg1_0_p1 x y u
private def dg1_1 (x y u : Rat) : Rat := 25 * u ^ 5 + 66 * y * u ^ 4 + 46 * y ^ 2 * u ^ 3 + 9 * y ^ 3 * u ^ 2 + 35 * x * u ^ 4 + 124 * x * y * u ^ 3 + 93 * x * y ^ 2 * u ^ 2 + 17 * x * y ^ 3 * u + 11 * x ^ 2 * u ^ 3 + 69 * x ^ 2 * y * u ^ 2 + 56 * x ^ 2 * y ^ 2 * u + 8 * x ^ 2 * y ^ 3 + x ^ 3 * u ^ 2 + 12 * x ^ 3 * y * u + 9 * x ^ 3 * y ^ 2 + x ^ 4 * y
private def dg1_2 (x y u : Rat) : Rat := 31 * u ^ 4 + 49 * y * u ^ 3 + 15 * y ^ 2 * u ^ 2 + 42 * x * u ^ 3 + 86 * x * y * u ^ 2 + 26 * x * y ^ 2 * u + 12 * x ^ 2 * u ^ 2 + 42 * x ^ 2 * y * u + 11 * x ^ 2 * y ^ 2 + x ^ 3 * u + 5 * x ^ 3 * y
private def dg1_3 (x y u : Rat) : Rat := 17 * u ^ 3 + 12 * y * u ^ 2 + 21 * x * u ^ 2 + 19 * x * y * u + 4 * x ^ 2 * u + 7 * x ^ 2 * y
private def dg1_4 (x y u : Rat) : Rat := 4 * u ^ 2 + 4 * x * u
private def dg2_0_p0 (x y u : Rat) : Rat := 12 * u ^ 6 + 17 * y * u ^ 5 + 5 * y ^ 2 * u ^ 4 + 52 * x * u ^ 5 + 87 * x * y * u ^ 4 + 34 * x * y ^ 2 * u ^ 3 + 3 * x * y ^ 3 * u ^ 2 + 71 * x ^ 2 * u ^ 4 + 130 * x ^ 2 * y * u ^ 3 + 53 * x ^ 2 * y ^ 2 * u ^ 2 + 5 * x ^ 2 * y ^ 3 * u + 40 * x ^ 3 * u ^ 3 + 74 * x ^ 3 * y * u ^ 2 + 28 * x ^ 3 * y ^ 2 * u
private def dg2_0_p1 (x y u : Rat) : Rat := 2 * x ^ 3 * y ^ 3 + 10 * x ^ 4 * u ^ 2 + 15 * x ^ 4 * y * u + 4 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def dg2_0 (x y u : Rat) : Rat := dg2_0_p0 x y u + dg2_0_p1 x y u
private def dg2_1 (x y u : Rat) : Rat := 22 * u ^ 5 + 13 * y * u ^ 4 + 96 * x * u ^ 4 + 80 * x * y * u ^ 3 + 11 * x * y ^ 2 * u ^ 2 + 113 * x ^ 2 * u ^ 3 + 111 * x ^ 2 * y * u ^ 2 + 18 * x ^ 2 * y ^ 2 * u + 45 * x ^ 3 * u ^ 2 + 49 * x ^ 3 * y * u + 7 * x ^ 3 * y ^ 2 + 6 * x ^ 4 * u + 5 * x ^ 4 * y
private def dg2_2 (x y u : Rat) : Rat := 10 * u ^ 4 + 51 * x * u ^ 3 + 14 * x * y * u ^ 2 + 53 * x ^ 2 * u ^ 2 + 21 * x ^ 2 * y * u + 12 * x ^ 3 * u + 7 * x ^ 3 * y
private def dg2_3 (x y u : Rat) : Rat := 8 * x * u ^ 2 + 8 * x ^ 2 * u
private def dg3_0_p0 (x y u : Rat) : Rat := 6 * u ^ 6 + 3 * y * u ^ 5 + 44 * x * u ^ 5 + 31 * x * y * u ^ 4 + 4 * x * y ^ 2 * u ^ 3 + 106 * x ^ 2 * u ^ 4 + 90 * x ^ 2 * y * u ^ 3 + 18 * x ^ 2 * y ^ 2 * u ^ 2 + x ^ 2 * y ^ 3 * u + 108 * x ^ 3 * u ^ 3 + 98 * x ^ 3 * y * u ^ 2 + 20 * x ^ 3 * y ^ 2 * u + x ^ 3 * y ^ 3 + 50 * x ^ 4 * u ^ 2
private def dg3_0_p1 (x y u : Rat) : Rat := 41 * x ^ 4 * y * u + 6 * x ^ 4 * y ^ 2 + 11 * x ^ 5 * u + 5 * x ^ 5 * y + x ^ 6
private def dg3_0 (x y u : Rat) : Rat := dg3_0_p0 x y u + dg3_0_p1 x y u
private def dg3_1 (x y u : Rat) : Rat := 4 * u ^ 5 + 52 * x * u ^ 4 + 16 * x * y * u ^ 3 + 149 * x ^ 2 * u ^ 3 + 64 * x ^ 2 * y * u ^ 2 + 4 * x ^ 2 * y ^ 2 * u + 145 * x ^ 3 * u ^ 2 + 65 * x ^ 3 * y * u + 4 * x ^ 3 * y ^ 2 + 50 * x ^ 4 * u + 17 * x ^ 4 * y + 6 * x ^ 5
private def dg3_2 (x y u : Rat) : Rat := 17 * x * u ^ 3 + 65 * x ^ 2 * u ^ 2 + 7 * x ^ 2 * y * u + 60 * x ^ 3 * u + 7 * x ^ 3 * y + 12 * x ^ 4
private def dg3_3 (x y u : Rat) : Rat := 8 * x ^ 2 * u + 8 * x ^ 3
private def dg4_1 (x y u : Rat) : Rat := 3 * u ^ 5 + 4 * y * u ^ 4 + y ^ 2 * u ^ 3 + 13 * x * u ^ 4 + 23 * x * y * u ^ 3 + 9 * x * y ^ 2 * u ^ 2 + x * y ^ 3 * u + 13 * x ^ 2 * u ^ 3 + 29 * x ^ 2 * y * u ^ 2 + 11 * x ^ 2 * y ^ 2 * u + x ^ 2 * y ^ 3 + 3 * x ^ 3 * u ^ 2 + 11 * x ^ 3 * y * u + 3 * x ^ 3 * y ^ 2 + x ^ 4 * y
private def dg4_2 (x y u : Rat) : Rat := 6 * u ^ 4 + 3 * y * u ^ 3 + 31 * x * u ^ 3 + 25 * x * y * u ^ 2 + 4 * x * y ^ 2 * u + 33 * x ^ 2 * u ^ 2 + 29 * x ^ 2 * y * u + 4 * x ^ 2 * y ^ 2 + 9 * x ^ 3 * u + 7 * x ^ 3 * y + x ^ 4
private def dg4_3 (x y u : Rat) : Rat := 3 * u ^ 3 + 19 * x * u ^ 2 + 5 * x * y * u + 20 * x ^ 2 * u + 5 * x ^ 2 * y + 4 * x ^ 3
private def dg4_4 (x y u : Rat) : Rat := 4 * x * u + 4 * x ^ 2
private def dg5_1 (x y u : Rat) : Rat := 3 * u ^ 5 + 4 * y * u ^ 4 + y ^ 2 * u ^ 3 + 7 * x * u ^ 4 + 12 * x * y * u ^ 3 + 3 * x * y ^ 2 * u ^ 2 + 4 * x ^ 2 * u ^ 3 + 12 * x ^ 2 * y * u ^ 2 + 3 * x ^ 2 * y ^ 2 * u + 4 * x ^ 3 * y * u + x ^ 3 * y ^ 2
private def dg5_2 (x y u : Rat) : Rat := 6 * u ^ 4 + 3 * y * u ^ 3 + 18 * x * u ^ 3 + 9 * x * y * u ^ 2 + 16 * x ^ 2 * u ^ 2 + 8 * x ^ 2 * y * u + 4 * x ^ 3 * u + 2 * x ^ 3 * y
private def dg5_3 (x y u : Rat) : Rat := 3 * u ^ 3 + 9 * x * u ^ 2 + 6 * x ^ 2 * u
private def dg6_0 (x y u : Rat) : Rat := u ^ 6 + 10 * y * u ^ 5 + 15 * y ^ 2 * u ^ 4 + 7 * y ^ 3 * u ^ 3 + y ^ 4 * u ^ 2 + x * u ^ 5 + 20 * x * y * u ^ 4 + 35 * x * y ^ 2 * u ^ 3 + 16 * x * y ^ 3 * u ^ 2 + 2 * x * y ^ 4 * u + 10 * x ^ 2 * y * u ^ 3 + 25 * x ^ 2 * y ^ 2 * u ^ 2 + 11 * x ^ 2 * y ^ 3 * u + x ^ 2 * y ^ 4 + 5 * x ^ 3 * y ^ 2 * u + 2 * x ^ 3 * y ^ 3
private def dg6_1 (x y u : Rat) : Rat := 13 * u ^ 5 + 43 * y * u ^ 4 + 31 * y ^ 2 * u ^ 3 + 6 * y ^ 3 * u ^ 2 + 19 * x * u ^ 4 + 85 * x * y * u ^ 3 + 63 * x * y ^ 2 * u ^ 2 + 11 * x * y ^ 3 * u + 6 * x ^ 2 * u ^ 3 + 48 * x ^ 2 * y * u ^ 2 + 37 * x ^ 2 * y ^ 2 * u + 5 * x ^ 2 * y ^ 3 + 6 * x ^ 3 * y * u + 5 * x ^ 3 * y ^ 2
private def dg6_2 (x y u : Rat) : Rat := 22 * u ^ 4 + 39 * y * u ^ 3 + 12 * y ^ 2 * u ^ 2 + 30 * x * u ^ 3 + 70 * x * y * u ^ 2 + 21 * x * y ^ 2 * u + 9 * x ^ 2 * u ^ 2 + 33 * x ^ 2 * y * u + 9 * x ^ 2 * y ^ 2 + x ^ 3 * u + 2 * x ^ 3 * y
private def dg6_3 (x y u : Rat) : Rat := 14 * u ^ 3 + 10 * y * u ^ 2 + 18 * x * u ^ 2 + 16 * x * y * u + 4 * x ^ 2 * u + 6 * x ^ 2 * y
private def dg6_4 (x y u : Rat) : Rat := 4 * u ^ 2 + 4 * x * u
private def dg7_0 (x y u : Rat) : Rat := 4 * u ^ 6 + 10 * y * u ^ 5 + 6 * y ^ 2 * u ^ 4 + y ^ 3 * u ^ 3 + 9 * x * u ^ 5 + 30 * x * y * u ^ 4 + 19 * x * y ^ 2 * u ^ 3 + 3 * x * y ^ 3 * u ^ 2 + 5 * x ^ 2 * u ^ 4 + 30 * x ^ 2 * y * u ^ 3 + 21 * x ^ 2 * y ^ 2 * u ^ 2 + 3 * x ^ 2 * y ^ 3 * u + 10 * x ^ 3 * y * u ^ 2 + 9 * x ^ 3 * y ^ 2 * u + x ^ 3 * y ^ 3 + x ^ 4 * y ^ 2
private def dg7_1 (x y u : Rat) : Rat := 14 * u ^ 5 + 16 * y * u ^ 4 + 4 * y ^ 2 * u ^ 3 + 44 * x * u ^ 4 + 59 * x * y * u ^ 3 + 18 * x * y ^ 2 * u ^ 2 + x * y ^ 3 * u + 40 * x ^ 2 * u ^ 3 + 65 * x ^ 2 * y * u ^ 2 + 20 * x ^ 2 * y ^ 2 * u + x ^ 2 * y ^ 3 + 10 * x ^ 3 * u ^ 2 + 24 * x ^ 3 * y * u + 6 * x ^ 3 * y ^ 2 + 2 * x ^ 4 * y
private def dg7_2 (x y u : Rat) : Rat := 12 * u ^ 4 + 6 * y * u ^ 3 + 42 * x * u ^ 3 + 30 * x * y * u ^ 2 + 3 * x * y ^ 2 * u + 36 * x ^ 2 * u ^ 2 + 33 * x ^ 2 * y * u + 3 * x ^ 2 * y ^ 2 + 7 * x ^ 3 * u + 9 * x ^ 3 * y + x ^ 4
private def dg7_3 (x y u : Rat) : Rat := 3 * u ^ 3 + 17 * x * u ^ 2 + 4 * x * y * u + 18 * x ^ 2 * u + 4 * x ^ 2 * y + 4 * x ^ 3
private def dg7_4 (x y u : Rat) : Rat := 4 * x * u + 4 * x ^ 2
private theorem cgEq0 (x y z u : Rat) : ck0 x y z u = cg0_0 x y u + z ^ 1 * cg0_1 x y u + z ^ 2 * cg0_2 x y u + z ^ 3 * cg0_3 x y u + z ^ 4 * cg0_4 x y u + z ^ 5 * cg0_5 x y u + z ^ 6 * cg0_6 x y u := by
  simp only [ck0, ck0_p0, ck0_p1, ck0_p2, ck0_p3, ck0_p4, ck0_p5, cg0_0, cg0_0_p0, cg0_0_p1, cg0_1, cg0_1_p0, cg0_1_p1, cg0_2, cg0_3, cg0_4, cg0_5, cg0_6]; try ring
private theorem cgEq1 (x y z u : Rat) : ck1 x y z u = cg1_0 x y u + z ^ 1 * cg1_1 x y u + z ^ 2 * cg1_2 x y u + z ^ 3 * cg1_3 x y u + z ^ 4 * cg1_4 x y u + z ^ 5 * cg1_5 x y u + z ^ 6 * cg1_6 x y u := by
  simp only [ck1, ck1_p0, ck1_p1, ck1_p2, ck1_p3, ck1_p4, cg1_0, cg1_0_p0, cg1_0_p1, cg1_1, cg1_1_p0, cg1_1_p1, cg1_2, cg1_3, cg1_4, cg1_5, cg1_6]; try ring
private theorem cgEq2 (x y z u : Rat) : ck2 x y z u = cg2_0 x y u + z ^ 1 * cg2_1 x y u + z ^ 2 * cg2_2 x y u + z ^ 3 * cg2_3 x y u + z ^ 4 * cg2_4 x y u + z ^ 5 * cg2_5 x y u + z ^ 6 * cg2_6 x y u := by
  simp only [ck2, ck2_p0, ck2_p1, ck2_p2, ck2_p3, ck2_p4, cg2_0, cg2_0_p0, cg2_0_p1, cg2_1, cg2_1_p0, cg2_1_p1, cg2_2, cg2_3, cg2_4, cg2_5, cg2_6]; try ring
private theorem cgEq3 (x y z u : Rat) : ck3 x y z u = cg3_0 x y u + z ^ 1 * cg3_1 x y u + z ^ 2 * cg3_2 x y u + z ^ 3 * cg3_3 x y u + z ^ 4 * cg3_4 x y u + z ^ 5 * cg3_5 x y u + z ^ 6 * cg3_6 x y u := by
  simp only [ck3, ck3_p0, ck3_p1, ck3_p2, ck3_p3, ck3_p4, ck3_p5, cg3_0, cg3_0_p0, cg3_0_p1, cg3_1, cg3_1_p0, cg3_1_p1, cg3_2, cg3_3, cg3_4, cg3_5, cg3_6]; try ring
private theorem cgEq4 (x y z u : Rat) : ck4 x y z u = cg4_0 x y u + z ^ 1 * cg4_1 x y u + z ^ 2 * cg4_2 x y u + z ^ 3 * cg4_3 x y u + z ^ 4 * cg4_4 x y u + z ^ 5 * cg4_5 x y u + z ^ 6 * cg4_6 x y u := by
  simp only [ck4, ck4_p0, ck4_p1, ck4_p2, ck4_p3, ck4_p4, ck4_p5, cg4_0, cg4_0_p0, cg4_0_p1, cg4_1, cg4_1_p0, cg4_1_p1, cg4_2, cg4_3, cg4_4, cg4_5, cg4_6]; try ring
private theorem cgEq5 (x y z u : Rat) : ck5 x y z u = cg5_0 x y u + z ^ 1 * cg5_1 x y u + z ^ 2 * cg5_2 x y u + z ^ 3 * cg5_3 x y u + z ^ 4 * cg5_4 x y u + z ^ 5 * cg5_5 x y u + z ^ 6 * cg5_6 x y u := by
  simp only [ck5, ck5_p0, ck5_p1, ck5_p2, ck5_p3, ck5_p4, cg5_0, cg5_0_p0, cg5_0_p1, cg5_1, cg5_1_p0, cg5_1_p1, cg5_2, cg5_3, cg5_4, cg5_5, cg5_6]; try ring
private theorem cgEq6 (x y z u : Rat) : ck6 x y z u = cg6_0 x y u + z ^ 1 * cg6_1 x y u + z ^ 2 * cg6_2 x y u + z ^ 3 * cg6_3 x y u + z ^ 4 * cg6_4 x y u + z ^ 5 * cg6_5 x y u + z ^ 6 * cg6_6 x y u := by
  simp only [ck6, ck6_p0, ck6_p1, ck6_p2, ck6_p3, ck6_p4, cg6_0, cg6_0_p0, cg6_0_p1, cg6_1, cg6_1_p0, cg6_1_p1, cg6_2, cg6_3, cg6_4, cg6_5, cg6_6]; try ring
private theorem cgEq7 (x y z u : Rat) : ck7 x y z u = cg7_0 x y u + z ^ 1 * cg7_1 x y u + z ^ 2 * cg7_2 x y u + z ^ 3 * cg7_3 x y u + z ^ 4 * cg7_4 x y u + z ^ 5 * cg7_5 x y u + z ^ 6 * cg7_6 x y u := by
  simp only [ck7, ck7_p0, ck7_p1, ck7_p2, ck7_p3, ck7_p4, ck7_p5, cg7_0, cg7_0_p0, cg7_0_p1, cg7_1, cg7_1_p0, cg7_1_p1, cg7_2, cg7_3, cg7_4, cg7_5, cg7_6]; try ring
private theorem dgEq0 (x y z u : Rat) : wk0 x y z u = dg0_0 x y u + z ^ 1 * dg0_1 x y u + z ^ 2 * dg0_2 x y u + z ^ 3 * dg0_3 x y u := by
  simp only [wk0, wk0_p0, wk0_p1, wk0_p2, wk0_p3, dg0_0, dg0_0_p0, dg0_0_p1, dg0_1, dg0_2, dg0_3]; try ring
private theorem dgEq1 (x y z u : Rat) : wk1 x y z u = dg1_0 x y u + z ^ 1 * dg1_1 x y u + z ^ 2 * dg1_2 x y u + z ^ 3 * dg1_3 x y u + z ^ 4 * dg1_4 x y u := by
  simp only [wk1, wk1_p0, wk1_p1, wk1_p2, wk1_p3, dg1_0, dg1_0_p0, dg1_0_p1, dg1_1, dg1_2, dg1_3, dg1_4]; try ring
private theorem dgEq2 (x y z u : Rat) : wk2 x y z u = dg2_0 x y u + z ^ 1 * dg2_1 x y u + z ^ 2 * dg2_2 x y u + z ^ 3 * dg2_3 x y u := by
  simp only [wk2, wk2_p0, wk2_p1, wk2_p2, dg2_0, dg2_0_p0, dg2_0_p1, dg2_1, dg2_2, dg2_3]; try ring
private theorem dgEq3 (x y z u : Rat) : wk3 x y z u = dg3_0 x y u + z ^ 1 * dg3_1 x y u + z ^ 2 * dg3_2 x y u + z ^ 3 * dg3_3 x y u := by
  simp only [wk3, wk3_p0, wk3_p1, wk3_p2, dg3_0, dg3_0_p0, dg3_0_p1, dg3_1, dg3_2, dg3_3]; try ring
private theorem dgEq4 (x y z u : Rat) : wk4 x y z u = z ^ 1 * dg4_1 x y u + z ^ 2 * dg4_2 x y u + z ^ 3 * dg4_3 x y u + z ^ 4 * dg4_4 x y u := by
  simp only [wk4, wk4_p0, wk4_p1, wk4_p2, dg4_1, dg4_2, dg4_3, dg4_4]; try ring
private theorem dgEq5 (x y z u : Rat) : wk5 x y z u = z ^ 1 * dg5_1 x y u + z ^ 2 * dg5_2 x y u + z ^ 3 * dg5_3 x y u := by
  simp only [wk5, wk5_p0, wk5_p1, dg5_1, dg5_2, dg5_3]; try ring
private theorem dgEq6 (x y z u : Rat) : wk6 x y z u = dg6_0 x y u + z ^ 1 * dg6_1 x y u + z ^ 2 * dg6_2 x y u + z ^ 3 * dg6_3 x y u + z ^ 4 * dg6_4 x y u := by
  simp only [wk6, wk6_p0, wk6_p1, wk6_p2, wk6_p3, dg6_0, dg6_1, dg6_2, dg6_3, dg6_4]; try ring
private theorem dgEq7 (x y z u : Rat) : wk7 x y z u = dg7_0 x y u + z ^ 1 * dg7_1 x y u + z ^ 2 * dg7_2 x y u + z ^ 3 * dg7_3 x y u + z ^ 4 * dg7_4 x y u := by
  simp only [wk7, wk7_p0, wk7_p1, wk7_p2, wk7_p3, dg7_0, dg7_1, dg7_2, dg7_3, dg7_4]; try ring
private def dlo0_p0 (x y u : Rat) : Rat := 24 * u ^ 12 + 104 * y * u ^ 11 + 170 * y ^ 2 * u ^ 10 + 136 * y ^ 3 * u ^ 9 + 57 * y ^ 4 * u ^ 8 + 12 * y ^ 5 * u ^ 7 + y ^ 6 * u ^ 6 + 60 * x * u ^ 11 + 238 * x * y * u ^ 10 + 274 * x * y ^ 2 * u ^ 9 + 37 * x * y ^ 3 * u ^ 8 - 124 * x * y ^ 4 * u ^ 7 - 86 * x * y ^ 5 * u ^ 6 - 22 * x * y ^ 6 * u ^ 5
private def dlo0_p1 (x y u : Rat) : Rat := -2 * x * y ^ 7 * u ^ 4 + 48 * x ^ 2 * u ^ 10 + 156 * x ^ 2 * y * u ^ 9 - 54 * x ^ 2 * y ^ 2 * u ^ 8 - 488 * x ^ 2 * y ^ 3 * u ^ 7 - 454 * x ^ 2 * y ^ 4 * u ^ 6 - 140 * x ^ 2 * y ^ 5 * u ^ 5 + 2 * x ^ 2 * y ^ 6 * u ^ 4 + 8 * x ^ 2 * y ^ 7 * u ^ 3 + x ^ 2 * y ^ 8 * u ^ 2 + 12 * x ^ 3 * u ^ 9 + 14 * x ^ 3 * y * u ^ 8 - 266 * x ^ 3 * y ^ 2 * u ^ 7 - 543 * x ^ 3 * y ^ 3 * u ^ 6
private def dlo0_p2 (x y u : Rat) : Rat := -218 * x ^ 3 * y ^ 4 * u ^ 5 + 121 * x ^ 3 * y ^ 5 * u ^ 4 + 108 * x ^ 3 * y ^ 6 * u ^ 3 + 26 * x ^ 3 * y ^ 7 * u ^ 2 + 2 * x ^ 3 * y ^ 8 * u - 8 * x ^ 4 * y * u ^ 7 - 124 * x ^ 4 * y ^ 2 * u ^ 6 - 146 * x ^ 4 * y ^ 3 * u ^ 5 + 181 * x ^ 4 * y ^ 4 * u ^ 4 + 284 * x ^ 4 * y ^ 5 * u ^ 3 + 122 * x ^ 4 * y ^ 6 * u ^ 2 + 20 * x ^ 4 * y ^ 7 * u + x ^ 4 * y ^ 8 - 16 * x ^ 5 * y ^ 2 * u ^ 5
private def dlo0_p3 (x y u : Rat) : Rat := 16 * x ^ 5 * y ^ 3 * u ^ 4 + 166 * x ^ 5 * y ^ 4 * u ^ 3 + 149 * x ^ 5 * y ^ 5 * u ^ 2 + 44 * x ^ 5 * y ^ 6 * u + 4 * x ^ 5 * y ^ 7 + 8 * x ^ 6 * y ^ 3 * u ^ 3 + 44 * x ^ 6 * y ^ 4 * u ^ 2 + 30 * x ^ 6 * y ^ 5 * u + 5 * x ^ 6 * y ^ 6 + 4 * x ^ 7 * y ^ 4 * u + 2 * x ^ 7 * y ^ 5
private def dlo0 (x y u : Rat) : Rat := dlo0_p0 x y u + dlo0_p1 x y u + dlo0_p2 x y u + dlo0_p3 x y u
private def dlo1_p0 (x y u : Rat) : Rat := -66 * u ^ 11 - 313 * y * u ^ 10 - 658 * y ^ 2 * u ^ 9 - 739 * y ^ 3 * u ^ 8 - 460 * y ^ 4 * u ^ 7 - 158 * y ^ 5 * u ^ 6 - 28 * y ^ 6 * u ^ 5 - 2 * y ^ 7 * u ^ 4 - 615 * x * u ^ 10 - 2266 * x * y * u ^ 9 - 3626 * x * y ^ 2 * u ^ 8 - 3016 * x * y ^ 3 * u ^ 7 - 1186 * x * y ^ 4 * u ^ 6 - 88 * x * y ^ 5 * u ^ 5
private def dlo1_p1 (x y u : Rat) : Rat := 81 * x * y ^ 6 * u ^ 4 + 24 * x * y ^ 7 * u ^ 3 + 2 * x * y ^ 8 * u ^ 2 - 1584 * x ^ 2 * u ^ 9 - 4777 * x ^ 2 * y * u ^ 8 - 5674 * x ^ 2 * y ^ 2 * u ^ 7 - 2591 * x ^ 2 * y ^ 3 * u ^ 6 + 744 * x ^ 2 * y ^ 4 * u ^ 5 + 1246 * x ^ 2 * y ^ 5 * u ^ 4 + 478 * x ^ 2 * y ^ 6 * u ^ 3 + 75 * x ^ 2 * y ^ 7 * u ^ 2 + 4 * x ^ 2 * y ^ 8 * u - 1875 * x ^ 3 * u ^ 8 - 4176 * x ^ 3 * y * u ^ 7
private def dlo1_p2 (x y u : Rat) : Rat := -2132 * x ^ 3 * y ^ 2 * u ^ 6 + 2678 * x ^ 3 * y ^ 3 * u ^ 5 + 4544 * x ^ 3 * y ^ 4 * u ^ 4 + 2584 * x ^ 3 * y ^ 5 * u ^ 3 + 658 * x ^ 3 * y ^ 6 * u ^ 2 + 70 * x ^ 3 * y ^ 7 * u + 2 * x ^ 3 * y ^ 8 - 1204 * x ^ 4 * u ^ 7 - 1382 * x ^ 4 * y * u ^ 6 + 2164 * x ^ 4 * y ^ 2 * u ^ 5 + 5430 * x ^ 4 * y ^ 3 * u ^ 4 + 4746 * x ^ 4 * y ^ 4 * u ^ 3 + 1929 * x ^ 4 * y ^ 5 * u ^ 2 + 346 * x ^ 4 * y ^ 6 * u
private def dlo1_p3 (x y u : Rat) : Rat := 21 * x ^ 4 * y ^ 7 - 448 * x ^ 5 * u ^ 6 + 172 * x ^ 5 * y * u ^ 5 + 2356 * x ^ 5 * y ^ 2 * u ^ 4 + 3208 * x ^ 5 * y ^ 3 * u ^ 3 + 2033 * x ^ 5 * y ^ 4 * u ^ 2 + 582 * x ^ 5 * y ^ 5 * u + 57 * x ^ 5 * y ^ 6 - 92 * x ^ 6 * u ^ 5 + 274 * x ^ 6 * y * u ^ 4 + 924 * x ^ 6 * y ^ 2 * u ^ 3 + 874 * x ^ 6 * y ^ 3 * u ^ 2 + 388 * x ^ 6 * y ^ 4 * u + 61 * x ^ 6 * y ^ 5
private def dlo1_p4 (x y u : Rat) : Rat := -8 * x ^ 7 * u ^ 4 + 80 * x ^ 7 * y * u ^ 3 + 170 * x ^ 7 * y ^ 2 * u ^ 2 + 108 * x ^ 7 * y ^ 3 * u + 27 * x ^ 7 * y ^ 4 + 8 * x ^ 8 * y * u ^ 2 + 12 * x ^ 8 * y ^ 2 * u + 4 * x ^ 8 * y ^ 3
private def dlo1 (x y u : Rat) : Rat := dlo1_p0 x y u + dlo1_p1 x y u + dlo1_p2 x y u + dlo1_p3 x y u + dlo1_p4 x y u
private def dlo2_p0 (x y u : Rat) : Rat := -603 * u ^ 10 - 2148 * y * u ^ 9 - 3161 * y ^ 2 * u ^ 8 - 2400 * y ^ 3 * u ^ 7 - 980 * y ^ 4 * u ^ 6 - 204 * y ^ 5 * u ^ 5 - 17 * y ^ 6 * u ^ 4 - 3220 * x * u ^ 9 - 9567 * x * y * u ^ 8 - 10986 * x * y ^ 2 * u ^ 7 - 5419 * x * y ^ 3 * u ^ 6 - 490 * x * y ^ 4 * u ^ 5 + 527 * x * y ^ 5 * u ^ 4 + 184 * x * y ^ 6 * u ^ 3
private def dlo2_p1 (x y u : Rat) : Rat := 18 * x * y ^ 7 * u ^ 2 - 6395 * x ^ 2 * u ^ 8 - 14960 * x ^ 2 * y * u ^ 7 - 10316 * x ^ 2 * y ^ 2 * u ^ 6 + 2174 * x ^ 2 * y ^ 3 * u ^ 5 + 6086 * x ^ 2 * y ^ 4 * u ^ 4 + 2888 * x ^ 2 * y ^ 5 * u ^ 3 + 549 * x ^ 2 * y ^ 6 * u ^ 2 + 36 * x ^ 2 * y ^ 7 * u - 6234 * x ^ 3 * u ^ 7 - 9409 * x ^ 3 * y * u ^ 6 + 3294 * x ^ 3 * y ^ 2 * u ^ 5 + 15165 * x ^ 3 * y ^ 3 * u ^ 4 + 11554 * x ^ 3 * y ^ 4 * u ^ 3
private def dlo2_p2 (x y u : Rat) : Rat := 3653 * x ^ 3 * y ^ 5 * u ^ 2 + 478 * x ^ 3 * y ^ 6 * u + 18 * x ^ 3 * y ^ 7 - 3267 * x ^ 4 * u ^ 6 - 966 * x ^ 4 * y * u ^ 5 + 10746 * x ^ 4 * y ^ 2 * u ^ 4 + 15124 * x ^ 4 * y ^ 3 * u ^ 3 + 8019 * x ^ 4 * y ^ 4 * u ^ 2 + 1770 * x ^ 4 * y ^ 5 * u + 130 * x ^ 4 * y ^ 6 - 936 * x ^ 5 * u ^ 5 + 1513 * x ^ 5 * y * u ^ 4 + 6502 * x ^ 5 * y ^ 2 * u ^ 3 + 6221 * x ^ 5 * y ^ 3 * u ^ 2
private def dlo2_p3 (x y u : Rat) : Rat := 2290 * x ^ 5 * y ^ 4 * u + 274 * x ^ 5 * y ^ 5 - 131 * x ^ 6 * u ^ 4 + 728 * x ^ 6 * y * u ^ 3 + 1741 * x ^ 6 * y ^ 2 * u ^ 2 + 1146 * x ^ 6 * y ^ 3 * u + 229 * x ^ 6 * y ^ 4 - 6 * x ^ 7 * u ^ 3 + 123 * x ^ 7 * y * u ^ 2 + 208 * x ^ 7 * y ^ 2 * u + 77 * x ^ 7 * y ^ 3 + 6 * x ^ 8 * y * u + 8 * x ^ 8 * y ^ 2
private def dlo2 (x y u : Rat) : Rat := dlo2_p0 x y u + dlo2_p1 x y u + dlo2_p2 x y u + dlo2_p3 x y u
private def dlo3_p0 (x y u : Rat) : Rat := -1444 * u ^ 9 - 4170 * y * u ^ 8 - 4666 * y ^ 2 * u ^ 7 - 2511 * y ^ 3 * u ^ 6 - 650 * y ^ 4 * u ^ 5 - 65 * y ^ 5 * u ^ 4 - 6483 * x * u ^ 8 - 15132 * x * y * u ^ 7 - 11737 * x * y ^ 2 * u ^ 6 - 2274 * x * y ^ 3 * u ^ 5 + 1229 * x * y ^ 4 * u ^ 4 + 604 * x * y ^ 5 * u ^ 3 + 72 * x * y ^ 6 * u ^ 2 - 11080 * x ^ 2 * u ^ 7
private def dlo3_p1 (x y u : Rat) : Rat := -18428 * x ^ 2 * y * u ^ 6 - 2664 * x ^ 2 * y ^ 2 * u ^ 5 + 10857 * x ^ 2 * y ^ 3 * u ^ 4 + 7516 * x ^ 2 * y ^ 4 * u ^ 3 + 1812 * x ^ 2 * y ^ 5 * u ^ 2 + 144 * x ^ 2 * y ^ 6 * u - 9180 * x ^ 3 * u ^ 6 - 6508 * x ^ 3 * y * u ^ 5 + 16153 * x ^ 3 * y ^ 2 * u ^ 4 + 21836 * x ^ 3 * y ^ 3 * u ^ 3 + 9410 * x ^ 3 * y ^ 4 * u ^ 2 + 1552 * x ^ 3 * y ^ 5 * u + 72 * x ^ 3 * y ^ 6 - 3910 * x ^ 4 * u ^ 5
private def dlo3_p2 (x y u : Rat) : Rat := 3237 * x ^ 4 * y * u ^ 4 + 17782 * x ^ 4 * y ^ 2 * u ^ 3 + 14951 * x ^ 4 * y ^ 3 * u ^ 2 + 4438 * x ^ 4 * y ^ 4 * u + 409 * x ^ 4 * y ^ 5 - 852 * x ^ 5 * u ^ 4 + 3004 * x ^ 5 * y * u ^ 3 + 7216 * x ^ 5 * y ^ 2 * u ^ 2 + 4126 * x ^ 5 * y ^ 3 * u + 665 * x ^ 5 * y ^ 4 - 84 * x ^ 6 * u ^ 3 + 806 * x ^ 6 * y * u ^ 2 + 1258 * x ^ 6 * y ^ 2 * u + 391 * x ^ 6 * y ^ 3
private def dlo3_p3 (x y u : Rat) : Rat := -3 * x ^ 7 * u ^ 2 + 84 * x ^ 7 * y * u + 78 * x ^ 7 * y ^ 2 + 3 * x ^ 8 * y
private def dlo3 (x y u : Rat) : Rat := dlo3_p0 x y u + dlo3_p1 x y u + dlo3_p2 x y u + dlo3_p3 x y u
private def dlo4_p0 (x y u : Rat) : Rat := -1969 * u ^ 8 - 4376 * y * u ^ 7 - 3510 * y ^ 2 * u ^ 6 - 1208 * y ^ 3 * u ^ 5 - 151 * y ^ 4 * u ^ 4 - 7638 * x * u ^ 7 - 12599 * x * y * u ^ 6 - 5010 * x * y ^ 2 * u ^ 5 + 1275 * x * y ^ 3 * u ^ 4 + 1136 * x * y ^ 4 * u ^ 3 + 174 * x * y ^ 5 * u ^ 2 - 11180 * x ^ 2 * u ^ 6 - 9670 * x ^ 2 * y * u ^ 5 + 7955 * x ^ 2 * y ^ 2 * u ^ 4
private def dlo4_p1 (x y u : Rat) : Rat := 10604 * x ^ 2 * y ^ 3 * u ^ 3 + 3492 * x ^ 2 * y ^ 4 * u ^ 2 + 348 * x ^ 2 * y ^ 5 * u - 7656 * x ^ 3 * u ^ 5 + 3024 * x ^ 3 * y * u ^ 4 + 19898 * x ^ 3 * y ^ 2 * u ^ 3 + 13445 * x ^ 3 * y ^ 3 * u ^ 2 + 2972 * x ^ 3 * y ^ 4 * u + 174 * x ^ 3 * y ^ 5 - 2503 * x ^ 4 * u ^ 4 + 6968 * x ^ 4 * y * u ^ 3 + 13762 * x ^ 4 * y ^ 2 * u ^ 2 + 6218 * x ^ 4 * y ^ 3 * u + 767 * x ^ 4 * y ^ 4
private def dlo4_p2 (x y u : Rat) : Rat := -382 * x ^ 5 * u ^ 3 + 2951 * x ^ 5 * y * u ^ 2 + 3640 * x ^ 5 * y ^ 2 * u + 894 * x ^ 5 * y ^ 3 - 24 * x ^ 6 * u ^ 2 + 482 * x ^ 6 * y * u + 321 * x ^ 6 * y ^ 2 + 28 * x ^ 7 * y
private def dlo4 (x y u : Rat) : Rat := dlo4_p0 x y u + dlo4_p1 x y u + dlo4_p2 x y u
private def dlo5_p0 (x y u : Rat) : Rat := -1624 * u ^ 7 - 2580 * y * u ^ 6 - 1326 * y ^ 2 * u ^ 5 - 221 * y ^ 3 * u ^ 4 - 5248 * x * u ^ 6 - 5068 * x * y * u ^ 5 + 229 * x * y ^ 2 * u ^ 4 + 1244 * x * y ^ 3 * u ^ 3 + 266 * x * y ^ 4 * u ^ 2 - 6124 * x ^ 2 * u ^ 5 + 406 * x ^ 2 * y * u ^ 4 + 7738 * x ^ 2 * y ^ 2 * u ^ 3 + 3985 * x ^ 2 * y ^ 3 * u ^ 2 + 532 * x ^ 2 * y ^ 4 * u
private def dlo5_p1 (x y u : Rat) : Rat := -3010 * x ^ 3 * u ^ 4 + 6720 * x ^ 3 * y * u ^ 3 + 10084 * x ^ 3 * y ^ 2 * u ^ 2 + 3354 * x ^ 3 * y ^ 3 * u + 266 * x ^ 3 * y ^ 4 - 512 * x ^ 4 * u ^ 3 + 4948 * x ^ 4 * y * u ^ 2 + 4500 * x ^ 4 * y ^ 2 * u + 834 * x ^ 4 * y ^ 3 + 6 * x ^ 5 * u ^ 2 + 1220 * x ^ 5 * y * u + 599 * x ^ 5 * y ^ 2 + 8 * x ^ 6 * u + 98 * x ^ 6 * y
private def dlo5 (x y u : Rat) : Rat := dlo5_p0 x y u + dlo5_p1 x y u
private def dlo6_p0 (x y u : Rat) : Rat := -795 * u ^ 6 - 856 * y * u ^ 5 - 262 * y ^ 2 * u ^ 4 - 24 * y ^ 3 * u ^ 3 - 3 * y ^ 4 * u ^ 2 - 2118 * x * u ^ 5 - 986 * x * y * u ^ 4 + 428 * x * y ^ 2 * u ^ 3 + 174 * x * y ^ 3 * u ^ 2 - 6 * x * y ^ 4 * u - 1877 * x ^ 2 * u ^ 4 + 1484 * x ^ 2 * y * u ^ 3 + 2073 * x ^ 2 * y ^ 2 * u ^ 2 + 420 * x ^ 2 * y ^ 3 * u
private def dlo6_p1 (x y u : Rat) : Rat := -3 * x ^ 2 * y ^ 4 - 572 * x ^ 3 * u ^ 3 + 2636 * x ^ 3 * y * u ^ 2 + 1814 * x ^ 3 * y ^ 2 * u + 222 * x ^ 3 * y ^ 3 - 13 * x ^ 4 * u ^ 2 + 1156 * x ^ 4 * y * u + 431 * x ^ 4 * y ^ 2 + 2 * x ^ 5 * u + 134 * x ^ 5 * y - 3 * x ^ 6
private def dlo6 (x y u : Rat) : Rat := dlo6_p0 x y u + dlo6_p1 x y u
private def dlo7_p0 (x y u : Rat) : Rat := -288 * u ^ 5 - 264 * y * u ^ 4 - 90 * y ^ 2 * u ^ 3 - 15 * y ^ 3 * u ^ 2 - 775 * x * u ^ 4 - 492 * x * y * u ^ 3 - 129 * x * y ^ 2 * u ^ 2 - 30 * x * y ^ 3 * u - 754 * x ^ 2 * u ^ 3 - 159 * x ^ 2 * y * u ^ 2 + 12 * x ^ 2 * y ^ 2 * u - 15 * x ^ 2 * y ^ 3 - 353 * x ^ 3 * u ^ 2 + 102 * x ^ 3 * y * u
private def dlo7_p1 (x y u : Rat) : Rat := 51 * x ^ 3 * y ^ 2 - 104 * x ^ 4 * u + 33 * x ^ 4 * y - 18 * x ^ 5
private def dlo7 (x y u : Rat) : Rat := dlo7_p0 x y u + dlo7_p1 x y u
private def dlo8 (x y u : Rat) : Rat := -121 * u ^ 4 - 108 * y * u ^ 3 - 27 * y ^ 2 * u ^ 2 - 368 * x * u ^ 3 - 266 * x * y * u ^ 2 - 54 * x * y ^ 2 * u - 411 * x ^ 2 * u ^ 2 - 208 * x ^ 2 * y * u - 27 * x ^ 2 * y ^ 2 - 202 * x ^ 3 * u - 50 * x ^ 3 * y - 38 * x ^ 4
private def dlo9 (x y u : Rat) : Rat := -44 * u ^ 3 - 22 * y * u ^ 2 - 120 * x * u ^ 2 - 44 * x * y * u - 108 * x ^ 2 * u - 22 * x ^ 2 * y - 32 * x ^ 3
private def dlo10 (x y u : Rat) : Rat := -8 * u ^ 2 - 16 * x * u - 8 * x ^ 2
private def dlo11 (x y u : Rat) : Rat := 0
private def dlo12 (x y u : Rat) : Rat := 0
private theorem dloGr (x y z u : Rat) : wzDlo x y z u = dlo0 x y u + z ^ 1 * dlo1 x y u + z ^ 2 * dlo2 x y u + z ^ 3 * dlo3 x y u + z ^ 4 * dlo4 x y u + z ^ 5 * dlo5 x y u + z ^ 6 * dlo6 x y u + z ^ 7 * dlo7 x y u + z ^ 8 * dlo8 x y u + z ^ 9 * dlo9 x y u + z ^ 10 * dlo10 x y u + z ^ 11 * dlo11 x y u + z ^ 12 * dlo12 x y u := by
  simp only [wzDlo, wzDlo_p0, wzDlo_p1, wzDlo_p2, wzDlo_p3, wzDlo_p4, wzDlo_p5, wzDlo_p6, wzDlo_p7, wzDlo_p8, wzDlo_p9, wzDlo_p10, wzDlo_p11, wzDlo_p12, wzDlo_p13, wzDlo_p14, wzDlo_p15, wzDlo_p16, wzDlo_p17, wzDlo_p18, wzDlo_p19, wzDlo_p20, wzDlo_p21, wzDlo_p22, wzDlo_p23, wzDlo_p24, dlo0, dlo0_p0, dlo0_p1, dlo0_p2, dlo0_p3, dlo1, dlo1_p0, dlo1_p1, dlo1_p2, dlo1_p3, dlo1_p4, dlo2, dlo2_p0, dlo2_p1, dlo2_p2, dlo2_p3, dlo3, dlo3_p0, dlo3_p1, dlo3_p2, dlo3_p3, dlo4, dlo4_p0, dlo4_p1, dlo4_p2, dlo5, dlo5_p0, dlo5_p1, dlo6, dlo6_p0, dlo6_p1, dlo7, dlo7_p0, dlo7_p1, dlo8, dlo9, dlo10, dlo11, dlo12]; try ring
/-- Coefficient of `z ^ 0`: 6 products. -/
private theorem gz0 (x y u : Rat) :
    cg0_0 x y u * dg0_0 x y u + cg1_0 x y u * dg1_0 x y u + cg2_0 x y u * dg2_0 x y u + cg3_0 x y u * dg3_0 x y u + cg6_0 x y u * dg6_0 x y u + cg7_0 x y u * dg7_0 x y u = dlo0 x y u := by
  simp only [cg0_0, cg0_0_p0, cg0_0_p1, cg1_0, cg1_0_p0, cg1_0_p1, cg2_0, cg2_0_p0, cg2_0_p1, cg3_0, cg3_0_p0, cg3_0_p1, cg6_0, cg6_0_p0, cg6_0_p1, cg7_0, cg7_0_p0, cg7_0_p1, dg0_0, dg0_0_p0, dg0_0_p1, dg1_0, dg1_0_p0, dg1_0_p1, dg2_0, dg2_0_p0, dg2_0_p1, dg3_0, dg3_0_p0, dg3_0_p1, dg6_0, dg7_0, dlo0, dlo0_p0, dlo0_p1, dlo0_p2, dlo0_p3]; try ring
/-- Coefficient of `z ^ 1`: 14 products. -/
private theorem gz1 (x y u : Rat) :
    cg0_0 x y u * dg0_1 x y u + cg0_1 x y u * dg0_0 x y u + cg1_0 x y u * dg1_1 x y u + cg1_1 x y u * dg1_0 x y u + cg2_0 x y u * dg2_1 x y u + cg2_1 x y u * dg2_0 x y u + cg3_0 x y u * dg3_1 x y u + cg3_1 x y u * dg3_0 x y u + cg4_0 x y u * dg4_1 x y u + cg5_0 x y u * dg5_1 x y u + cg6_0 x y u * dg6_1 x y u + cg6_1 x y u * dg6_0 x y u + cg7_0 x y u * dg7_1 x y u + cg7_1 x y u * dg7_0 x y u = dlo1 x y u := by
  simp only [cg0_0, cg0_0_p0, cg0_0_p1, cg0_1, cg0_1_p0, cg0_1_p1, cg1_0, cg1_0_p0, cg1_0_p1, cg1_1, cg1_1_p0, cg1_1_p1, cg2_0, cg2_0_p0, cg2_0_p1, cg2_1, cg2_1_p0, cg2_1_p1, cg3_0, cg3_0_p0, cg3_0_p1, cg3_1, cg3_1_p0, cg3_1_p1, cg4_0, cg4_0_p0, cg4_0_p1, cg5_0, cg5_0_p0, cg5_0_p1, cg6_0, cg6_0_p0, cg6_0_p1, cg6_1, cg6_1_p0, cg6_1_p1, cg7_0, cg7_0_p0, cg7_0_p1, cg7_1, cg7_1_p0, cg7_1_p1, dg0_0, dg0_0_p0, dg0_0_p1, dg0_1, dg1_0, dg1_0_p0, dg1_0_p1, dg1_1, dg2_0, dg2_0_p0, dg2_0_p1, dg2_1, dg3_0, dg3_0_p0, dg3_0_p1, dg3_1, dg4_1, dg5_1, dg6_0, dg6_1, dg7_0, dg7_1, dlo1, dlo1_p0, dlo1_p1, dlo1_p2, dlo1_p3, dlo1_p4]; try ring
/-- Coefficient of `z ^ 2`: 22 products. -/
private theorem gz2 (x y u : Rat) :
    cg0_0 x y u * dg0_2 x y u + cg0_1 x y u * dg0_1 x y u + cg0_2 x y u * dg0_0 x y u + cg1_0 x y u * dg1_2 x y u + cg1_1 x y u * dg1_1 x y u + cg1_2 x y u * dg1_0 x y u + cg2_0 x y u * dg2_2 x y u + cg2_1 x y u * dg2_1 x y u + cg2_2 x y u * dg2_0 x y u + cg3_0 x y u * dg3_2 x y u + cg3_1 x y u * dg3_1 x y u + cg3_2 x y u * dg3_0 x y u + cg4_0 x y u * dg4_2 x y u + cg4_1 x y u * dg4_1 x y u + cg5_0 x y u * dg5_2 x y u + cg5_1 x y u * dg5_1 x y u + cg6_0 x y u * dg6_2 x y u + cg6_1 x y u * dg6_1 x y u + cg6_2 x y u * dg6_0 x y u + cg7_0 x y u * dg7_2 x y u + cg7_1 x y u * dg7_1 x y u + cg7_2 x y u * dg7_0 x y u = dlo2 x y u := by
  simp only [cg0_0, cg0_0_p0, cg0_0_p1, cg0_1, cg0_1_p0, cg0_1_p1, cg0_2, cg1_0, cg1_0_p0, cg1_0_p1, cg1_1, cg1_1_p0, cg1_1_p1, cg1_2, cg2_0, cg2_0_p0, cg2_0_p1, cg2_1, cg2_1_p0, cg2_1_p1, cg2_2, cg3_0, cg3_0_p0, cg3_0_p1, cg3_1, cg3_1_p0, cg3_1_p1, cg3_2, cg4_0, cg4_0_p0, cg4_0_p1, cg4_1, cg4_1_p0, cg4_1_p1, cg5_0, cg5_0_p0, cg5_0_p1, cg5_1, cg5_1_p0, cg5_1_p1, cg6_0, cg6_0_p0, cg6_0_p1, cg6_1, cg6_1_p0, cg6_1_p1, cg6_2, cg7_0, cg7_0_p0, cg7_0_p1, cg7_1, cg7_1_p0, cg7_1_p1, cg7_2, dg0_0, dg0_0_p0, dg0_0_p1, dg0_1, dg0_2, dg1_0, dg1_0_p0, dg1_0_p1, dg1_1, dg1_2, dg2_0, dg2_0_p0, dg2_0_p1, dg2_1, dg2_2, dg3_0, dg3_0_p0, dg3_0_p1, dg3_1, dg3_2, dg4_1, dg4_2, dg5_1, dg5_2, dg6_0, dg6_1, dg6_2, dg7_0, dg7_1, dg7_2, dlo2, dlo2_p0, dlo2_p1, dlo2_p2, dlo2_p3]; try ring
/-- Coefficient of `z ^ 3`: 30 products. -/
private theorem gz3 (x y u : Rat) :
    cg0_0 x y u * dg0_3 x y u + cg0_1 x y u * dg0_2 x y u + cg0_2 x y u * dg0_1 x y u + cg0_3 x y u * dg0_0 x y u + cg1_0 x y u * dg1_3 x y u + cg1_1 x y u * dg1_2 x y u + cg1_2 x y u * dg1_1 x y u + cg1_3 x y u * dg1_0 x y u + cg2_0 x y u * dg2_3 x y u + cg2_1 x y u * dg2_2 x y u + cg2_2 x y u * dg2_1 x y u + cg2_3 x y u * dg2_0 x y u + cg3_0 x y u * dg3_3 x y u + cg3_1 x y u * dg3_2 x y u + cg3_2 x y u * dg3_1 x y u + cg3_3 x y u * dg3_0 x y u + cg4_0 x y u * dg4_3 x y u + cg4_1 x y u * dg4_2 x y u + cg4_2 x y u * dg4_1 x y u + cg5_0 x y u * dg5_3 x y u + cg5_1 x y u * dg5_2 x y u + cg5_2 x y u * dg5_1 x y u + cg6_0 x y u * dg6_3 x y u + cg6_1 x y u * dg6_2 x y u + cg6_2 x y u * dg6_1 x y u + cg6_3 x y u * dg6_0 x y u + cg7_0 x y u * dg7_3 x y u + cg7_1 x y u * dg7_2 x y u + cg7_2 x y u * dg7_1 x y u + cg7_3 x y u * dg7_0 x y u = dlo3 x y u := by
  simp only [cg0_0, cg0_0_p0, cg0_0_p1, cg0_1, cg0_1_p0, cg0_1_p1, cg0_2, cg0_3, cg1_0, cg1_0_p0, cg1_0_p1, cg1_1, cg1_1_p0, cg1_1_p1, cg1_2, cg1_3, cg2_0, cg2_0_p0, cg2_0_p1, cg2_1, cg2_1_p0, cg2_1_p1, cg2_2, cg2_3, cg3_0, cg3_0_p0, cg3_0_p1, cg3_1, cg3_1_p0, cg3_1_p1, cg3_2, cg3_3, cg4_0, cg4_0_p0, cg4_0_p1, cg4_1, cg4_1_p0, cg4_1_p1, cg4_2, cg5_0, cg5_0_p0, cg5_0_p1, cg5_1, cg5_1_p0, cg5_1_p1, cg5_2, cg6_0, cg6_0_p0, cg6_0_p1, cg6_1, cg6_1_p0, cg6_1_p1, cg6_2, cg6_3, cg7_0, cg7_0_p0, cg7_0_p1, cg7_1, cg7_1_p0, cg7_1_p1, cg7_2, cg7_3, dg0_0, dg0_0_p0, dg0_0_p1, dg0_1, dg0_2, dg0_3, dg1_0, dg1_0_p0, dg1_0_p1, dg1_1, dg1_2, dg1_3, dg2_0, dg2_0_p0, dg2_0_p1, dg2_1, dg2_2, dg2_3, dg3_0, dg3_0_p0, dg3_0_p1, dg3_1, dg3_2, dg3_3, dg4_1, dg4_2, dg4_3, dg5_1, dg5_2, dg5_3, dg6_0, dg6_1, dg6_2, dg6_3, dg7_0, dg7_1, dg7_2, dg7_3, dlo3, dlo3_p0, dlo3_p1, dlo3_p2, dlo3_p3]; try ring
/-- Coefficient of `z ^ 4`: 34 products. -/
private theorem gz4 (x y u : Rat) :
    cg0_1 x y u * dg0_3 x y u + cg0_2 x y u * dg0_2 x y u + cg0_3 x y u * dg0_1 x y u + cg0_4 x y u * dg0_0 x y u + cg1_0 x y u * dg1_4 x y u + cg1_1 x y u * dg1_3 x y u + cg1_2 x y u * dg1_2 x y u + cg1_3 x y u * dg1_1 x y u + cg1_4 x y u * dg1_0 x y u + cg2_1 x y u * dg2_3 x y u + cg2_2 x y u * dg2_2 x y u + cg2_3 x y u * dg2_1 x y u + cg2_4 x y u * dg2_0 x y u + cg3_1 x y u * dg3_3 x y u + cg3_2 x y u * dg3_2 x y u + cg3_3 x y u * dg3_1 x y u + cg3_4 x y u * dg3_0 x y u + cg4_0 x y u * dg4_4 x y u + cg4_1 x y u * dg4_3 x y u + cg4_2 x y u * dg4_2 x y u + cg4_3 x y u * dg4_1 x y u + cg5_1 x y u * dg5_3 x y u + cg5_2 x y u * dg5_2 x y u + cg5_3 x y u * dg5_1 x y u + cg6_0 x y u * dg6_4 x y u + cg6_1 x y u * dg6_3 x y u + cg6_2 x y u * dg6_2 x y u + cg6_3 x y u * dg6_1 x y u + cg6_4 x y u * dg6_0 x y u + cg7_0 x y u * dg7_4 x y u + cg7_1 x y u * dg7_3 x y u + cg7_2 x y u * dg7_2 x y u + cg7_3 x y u * dg7_1 x y u + cg7_4 x y u * dg7_0 x y u = dlo4 x y u := by
  simp only [cg0_1, cg0_1_p0, cg0_1_p1, cg0_2, cg0_3, cg0_4, cg1_0, cg1_0_p0, cg1_0_p1, cg1_1, cg1_1_p0, cg1_1_p1, cg1_2, cg1_3, cg1_4, cg2_1, cg2_1_p0, cg2_1_p1, cg2_2, cg2_3, cg2_4, cg3_1, cg3_1_p0, cg3_1_p1, cg3_2, cg3_3, cg3_4, cg4_0, cg4_0_p0, cg4_0_p1, cg4_1, cg4_1_p0, cg4_1_p1, cg4_2, cg4_3, cg5_1, cg5_1_p0, cg5_1_p1, cg5_2, cg5_3, cg6_0, cg6_0_p0, cg6_0_p1, cg6_1, cg6_1_p0, cg6_1_p1, cg6_2, cg6_3, cg6_4, cg7_0, cg7_0_p0, cg7_0_p1, cg7_1, cg7_1_p0, cg7_1_p1, cg7_2, cg7_3, cg7_4, dg0_0, dg0_0_p0, dg0_0_p1, dg0_1, dg0_2, dg0_3, dg1_0, dg1_0_p0, dg1_0_p1, dg1_1, dg1_2, dg1_3, dg1_4, dg2_0, dg2_0_p0, dg2_0_p1, dg2_1, dg2_2, dg2_3, dg3_0, dg3_0_p0, dg3_0_p1, dg3_1, dg3_2, dg3_3, dg4_1, dg4_2, dg4_3, dg4_4, dg5_1, dg5_2, dg5_3, dg6_0, dg6_1, dg6_2, dg6_3, dg6_4, dg7_0, dg7_1, dg7_2, dg7_3, dg7_4, dlo4, dlo4_p0, dlo4_p1, dlo4_p2]; try ring
/-- Coefficient of `z ^ 5`: 34 products. -/
private theorem gz5 (x y u : Rat) :
    cg0_2 x y u * dg0_3 x y u + cg0_3 x y u * dg0_2 x y u + cg0_4 x y u * dg0_1 x y u + cg0_5 x y u * dg0_0 x y u + cg1_1 x y u * dg1_4 x y u + cg1_2 x y u * dg1_3 x y u + cg1_3 x y u * dg1_2 x y u + cg1_4 x y u * dg1_1 x y u + cg1_5 x y u * dg1_0 x y u + cg2_2 x y u * dg2_3 x y u + cg2_3 x y u * dg2_2 x y u + cg2_4 x y u * dg2_1 x y u + cg2_5 x y u * dg2_0 x y u + cg3_2 x y u * dg3_3 x y u + cg3_3 x y u * dg3_2 x y u + cg3_4 x y u * dg3_1 x y u + cg3_5 x y u * dg3_0 x y u + cg4_1 x y u * dg4_4 x y u + cg4_2 x y u * dg4_3 x y u + cg4_3 x y u * dg4_2 x y u + cg4_4 x y u * dg4_1 x y u + cg5_2 x y u * dg5_3 x y u + cg5_3 x y u * dg5_2 x y u + cg5_4 x y u * dg5_1 x y u + cg6_1 x y u * dg6_4 x y u + cg6_2 x y u * dg6_3 x y u + cg6_3 x y u * dg6_2 x y u + cg6_4 x y u * dg6_1 x y u + cg6_5 x y u * dg6_0 x y u + cg7_1 x y u * dg7_4 x y u + cg7_2 x y u * dg7_3 x y u + cg7_3 x y u * dg7_2 x y u + cg7_4 x y u * dg7_1 x y u + cg7_5 x y u * dg7_0 x y u = dlo5 x y u := by
  simp only [cg0_2, cg0_3, cg0_4, cg0_5, cg1_1, cg1_1_p0, cg1_1_p1, cg1_2, cg1_3, cg1_4, cg1_5, cg2_2, cg2_3, cg2_4, cg2_5, cg3_2, cg3_3, cg3_4, cg3_5, cg4_1, cg4_1_p0, cg4_1_p1, cg4_2, cg4_3, cg4_4, cg5_2, cg5_3, cg5_4, cg6_1, cg6_1_p0, cg6_1_p1, cg6_2, cg6_3, cg6_4, cg6_5, cg7_1, cg7_1_p0, cg7_1_p1, cg7_2, cg7_3, cg7_4, cg7_5, dg0_0, dg0_0_p0, dg0_0_p1, dg0_1, dg0_2, dg0_3, dg1_0, dg1_0_p0, dg1_0_p1, dg1_1, dg1_2, dg1_3, dg1_4, dg2_0, dg2_0_p0, dg2_0_p1, dg2_1, dg2_2, dg2_3, dg3_0, dg3_0_p0, dg3_0_p1, dg3_1, dg3_2, dg3_3, dg4_1, dg4_2, dg4_3, dg4_4, dg5_1, dg5_2, dg5_3, dg6_0, dg6_1, dg6_2, dg6_3, dg6_4, dg7_0, dg7_1, dg7_2, dg7_3, dg7_4, dlo5, dlo5_p0, dlo5_p1]; try ring
/-- Coefficient of `z ^ 6`: 34 products. -/
private theorem gz6 (x y u : Rat) :
    cg0_3 x y u * dg0_3 x y u + cg0_4 x y u * dg0_2 x y u + cg0_5 x y u * dg0_1 x y u + cg0_6 x y u * dg0_0 x y u + cg1_2 x y u * dg1_4 x y u + cg1_3 x y u * dg1_3 x y u + cg1_4 x y u * dg1_2 x y u + cg1_5 x y u * dg1_1 x y u + cg1_6 x y u * dg1_0 x y u + cg2_3 x y u * dg2_3 x y u + cg2_4 x y u * dg2_2 x y u + cg2_5 x y u * dg2_1 x y u + cg2_6 x y u * dg2_0 x y u + cg3_3 x y u * dg3_3 x y u + cg3_4 x y u * dg3_2 x y u + cg3_6 x y u * dg3_0 x y u + cg3_5 x y u * dg3_1 x y u + cg4_2 x y u * dg4_4 x y u + cg4_3 x y u * dg4_3 x y u + cg4_4 x y u * dg4_2 x y u + cg4_5 x y u * dg4_1 x y u + cg5_3 x y u * dg5_3 x y u + cg5_4 x y u * dg5_2 x y u + cg5_5 x y u * dg5_1 x y u + cg6_2 x y u * dg6_4 x y u + cg6_3 x y u * dg6_3 x y u + cg6_4 x y u * dg6_2 x y u + cg6_5 x y u * dg6_1 x y u + cg6_6 x y u * dg6_0 x y u + cg7_2 x y u * dg7_4 x y u + cg7_3 x y u * dg7_3 x y u + cg7_4 x y u * dg7_2 x y u + cg7_5 x y u * dg7_1 x y u + cg7_6 x y u * dg7_0 x y u = dlo6 x y u := by
  simp only [cg0_3, cg0_4, cg0_5, cg0_6, cg1_2, cg1_3, cg1_4, cg1_5, cg1_6, cg2_3, cg2_4, cg2_5, cg2_6, cg3_3, cg3_4, cg3_5, cg3_6, cg4_2, cg4_3, cg4_4, cg4_5, cg5_3, cg5_4, cg5_5, cg6_2, cg6_3, cg6_4, cg6_5, cg6_6, cg7_2, cg7_3, cg7_4, cg7_5, cg7_6, dg0_0, dg0_0_p0, dg0_0_p1, dg0_1, dg0_2, dg0_3, dg1_0, dg1_0_p0, dg1_0_p1, dg1_1, dg1_2, dg1_3, dg1_4, dg2_0, dg2_0_p0, dg2_0_p1, dg2_1, dg2_2, dg2_3, dg3_0, dg3_0_p0, dg3_0_p1, dg3_1, dg3_2, dg3_3, dg4_1, dg4_2, dg4_3, dg4_4, dg5_1, dg5_2, dg5_3, dg6_0, dg6_1, dg6_2, dg6_3, dg6_4, dg7_0, dg7_1, dg7_2, dg7_3, dg7_4, dlo6, dlo6_p0, dlo6_p1]; try ring
/-- Coefficient of `z ^ 7`: 28 products. -/
private theorem gz7 (x y u : Rat) :
    cg0_4 x y u * dg0_3 x y u + cg0_5 x y u * dg0_2 x y u + cg0_6 x y u * dg0_1 x y u + cg1_3 x y u * dg1_4 x y u + cg1_4 x y u * dg1_3 x y u + cg1_5 x y u * dg1_2 x y u + cg1_6 x y u * dg1_1 x y u + cg2_4 x y u * dg2_3 x y u + cg2_5 x y u * dg2_2 x y u + cg2_6 x y u * dg2_1 x y u + cg3_4 x y u * dg3_3 x y u + cg3_6 x y u * dg3_1 x y u + cg3_5 x y u * dg3_2 x y u + cg4_3 x y u * dg4_4 x y u + cg4_4 x y u * dg4_3 x y u + cg4_5 x y u * dg4_2 x y u + cg4_6 x y u * dg4_1 x y u + cg5_4 x y u * dg5_3 x y u + cg5_5 x y u * dg5_2 x y u + cg5_6 x y u * dg5_1 x y u + cg6_3 x y u * dg6_4 x y u + cg6_4 x y u * dg6_3 x y u + cg6_5 x y u * dg6_2 x y u + cg6_6 x y u * dg6_1 x y u + cg7_3 x y u * dg7_4 x y u + cg7_4 x y u * dg7_3 x y u + cg7_5 x y u * dg7_2 x y u + cg7_6 x y u * dg7_1 x y u = dlo7 x y u := by
  simp only [cg0_4, cg0_5, cg0_6, cg1_3, cg1_4, cg1_5, cg1_6, cg2_4, cg2_5, cg2_6, cg3_4, cg3_5, cg3_6, cg4_3, cg4_4, cg4_5, cg4_6, cg5_4, cg5_5, cg5_6, cg6_3, cg6_4, cg6_5, cg6_6, cg7_3, cg7_4, cg7_5, cg7_6, dg0_1, dg0_2, dg0_3, dg1_1, dg1_2, dg1_3, dg1_4, dg2_1, dg2_2, dg2_3, dg3_1, dg3_2, dg3_3, dg4_1, dg4_2, dg4_3, dg4_4, dg5_1, dg5_2, dg5_3, dg6_1, dg6_2, dg6_3, dg6_4, dg7_1, dg7_2, dg7_3, dg7_4, dlo7, dlo7_p0, dlo7_p1]; try ring
/-- Coefficient of `z ^ 8`: 20 products. -/
private theorem gz8 (x y u : Rat) :
    cg0_5 x y u * dg0_3 x y u + cg0_6 x y u * dg0_2 x y u + cg1_4 x y u * dg1_4 x y u + cg1_5 x y u * dg1_3 x y u + cg1_6 x y u * dg1_2 x y u + cg2_5 x y u * dg2_3 x y u + cg2_6 x y u * dg2_2 x y u + cg3_6 x y u * dg3_2 x y u + cg3_5 x y u * dg3_3 x y u + cg4_4 x y u * dg4_4 x y u + cg4_5 x y u * dg4_3 x y u + cg4_6 x y u * dg4_2 x y u + cg5_5 x y u * dg5_3 x y u + cg5_6 x y u * dg5_2 x y u + cg6_4 x y u * dg6_4 x y u + cg6_5 x y u * dg6_3 x y u + cg6_6 x y u * dg6_2 x y u + cg7_4 x y u * dg7_4 x y u + cg7_5 x y u * dg7_3 x y u + cg7_6 x y u * dg7_2 x y u = dlo8 x y u := by
  simp only [cg0_5, cg0_6, cg1_4, cg1_5, cg1_6, cg2_5, cg2_6, cg3_5, cg3_6, cg4_4, cg4_5, cg4_6, cg5_5, cg5_6, cg6_4, cg6_5, cg6_6, cg7_4, cg7_5, cg7_6, dg0_2, dg0_3, dg1_2, dg1_3, dg1_4, dg2_2, dg2_3, dg3_2, dg3_3, dg4_2, dg4_3, dg4_4, dg5_2, dg5_3, dg6_2, dg6_3, dg6_4, dg7_2, dg7_3, dg7_4, dlo8]; try ring
/-- Coefficient of `z ^ 9`: 12 products. -/
private theorem gz9 (x y u : Rat) :
    cg0_6 x y u * dg0_3 x y u + cg1_5 x y u * dg1_4 x y u + cg1_6 x y u * dg1_3 x y u + cg2_6 x y u * dg2_3 x y u + cg3_6 x y u * dg3_3 x y u + cg4_5 x y u * dg4_4 x y u + cg4_6 x y u * dg4_3 x y u + cg5_6 x y u * dg5_3 x y u + cg6_5 x y u * dg6_4 x y u + cg6_6 x y u * dg6_3 x y u + cg7_5 x y u * dg7_4 x y u + cg7_6 x y u * dg7_3 x y u = dlo9 x y u := by
  simp only [cg0_6, cg1_5, cg1_6, cg2_6, cg3_6, cg4_5, cg4_6, cg5_6, cg6_5, cg6_6, cg7_5, cg7_6, dg0_3, dg1_3, dg1_4, dg2_3, dg3_3, dg4_3, dg4_4, dg5_3, dg6_3, dg6_4, dg7_3, dg7_4, dlo9]; try ring
/-- Coefficient of `z ^ 10`: 4 products. -/
private theorem gz10 (x y u : Rat) :
    cg1_6 x y u * dg1_4 x y u + cg4_6 x y u * dg4_4 x y u + cg6_6 x y u * dg6_4 x y u + cg7_6 x y u * dg7_4 x y u = dlo10 x y u := by
  simp only [cg1_6, cg4_6, cg6_6, cg7_6, dg1_4, dg4_4, dg6_4, dg7_4, dlo10]; try ring
/-- Coefficient of `z ^ 11`: 0 products. -/
private theorem gz11 (x y u : Rat) :
    0 = dlo11 x y u := by
  simp only [dlo11]; try ring
/-- Coefficient of `z ^ 12`: 0 products. -/
private theorem gz12 (x y u : Rat) :
    0 = dlo12 x y u := by
  simp only [dlo12]; try ring

end BunkbedTMGradedLo

open Bunkbed Bunkbed.Hyper Bunkbed.TM BunkbedTMGradedLo in
/-- **The first eight class products.** -/
theorem solution (x y z u : Rat) :
    ck0 x y z u * wk0 x y z u + ck1 x y z u * wk1 x y z u + ck2 x y z u * wk2 x y z u + ck3 x y z u * wk3 x y z u + ck4 x y z u * wk4 x y z u + ck5 x y z u * wk5 x y z u + ck6 x y z u * wk6 x y z u + ck7 x y z u * wk7 x y z u
      = wzDlo x y z u := by
  rw [cgEq0, cgEq1, cgEq2, cgEq3, cgEq4, cgEq5, cgEq6, cgEq7]
  rw [dgEq0, dgEq1, dgEq2, dgEq3, dgEq4, dgEq5, dgEq6, dgEq7]
  rw [dloGr]
  linear_combination gz0 x y u + z ^ 1 * gz1 x y u + z ^ 2 * gz2 x y u + z ^ 3 * gz3 x y u + z ^ 4 * gz4 x y u + z ^ 5 * gz5 x y u + z ^ 6 * gz6 x y u + z ^ 7 * gz7 x y u + z ^ 8 * gz8 x y u + z ^ 9 * gz9 x y u + z ^ 10 * gz10 x y u + z ^ 11 * gz11 x y u + z ^ 12 * gz12 x y u

#print axioms solution
