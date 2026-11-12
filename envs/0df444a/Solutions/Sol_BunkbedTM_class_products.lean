-- Prove2me | solution 1 for BunkbedTM.class_products
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T16:53:18.844482+00:00
-- url     : https://prove2.me/submissions/ab52f11d-8e99-4338-a313-67b4f0a6aaab

import Definitions.Def_BunkbedTransferPartial
import Definitions.Def_BunkbedWZPoly
import Theorems.Thm_BunkbedTM_class_products_lo

/-!
# The fifteen class products are the difference polynomial

`Σ_{k < 15} ck k * wk k = wzDiffPoly`. The first eight products are `wzDlo`, by the imported
`BunkbedTM.class_products_lo`; this file checks the remaining seven against
`wzDiffPoly - wzDlo`, again one power of `z` at a time. The right-hand sides of the thirteen
graded identities are the cofactors `wzDet ^ (6-n) * wzR n` of `wzDiffPoly` minus the
corresponding graded piece of `wzDlo`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

open Bunkbed Bunkbed.Hyper Bunkbed.TM Finset

namespace BunkbedTMGradedHi

private def cg8_0_p0 (x y u : Rat) : Rat := 24 * u ^ 6 + 72 * y * u ^ 5 + 78 * y ^ 2 * u ^ 4 + 40 * y ^ 3 * u ^ 3 + 10 * y ^ 4 * u ^ 2 + y ^ 5 * u + 70 * x * u ^ 5 + 195 * x * y * u ^ 4 + 186 * x * y ^ 2 * u ^ 3 + 79 * x * y ^ 3 * u ^ 2 + 15 * x * y ^ 4 * u + x * y ^ 5 + 76 * x ^ 2 * u ^ 4 + 192 * x ^ 2 * y * u ^ 3
private def cg8_0_p1 (x y u : Rat) : Rat := 153 * x ^ 2 * y ^ 2 * u ^ 2 + 48 * x ^ 2 * y ^ 3 * u + 5 * x ^ 2 * y ^ 4 + 38 * x ^ 3 * u ^ 3 + 83 * x ^ 3 * y * u ^ 2 + 50 * x ^ 3 * y ^ 2 * u + 9 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 15 * x ^ 4 * y * u + 5 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg8_0 (x y u : Rat) : Rat := cg8_0_p0 x y u + cg8_0_p1 x y u
private def cg8_1_p0 (x y u : Rat) : Rat := 68 * u ^ 5 + 150 * y * u ^ 4 + 116 * y ^ 2 * u ^ 3 + 39 * y ^ 3 * u ^ 2 + 5 * y ^ 4 * u + 166 * x * u ^ 4 + 339 * x * y * u ^ 3 + 224 * x * y ^ 2 * u ^ 2 + 58 * x * y ^ 3 * u + 5 * x * y ^ 4 + 141 * x ^ 2 * u ^ 3 + 254 * x ^ 2 * y * u ^ 2 + 130 * x ^ 2 * y ^ 2 * u + 19 * x ^ 2 * y ^ 3
private def cg8_1_p1 (x y u : Rat) : Rat := 51 * x ^ 3 * u ^ 2 + 71 * x ^ 3 * y * u + 22 * x ^ 3 * y ^ 2 + 8 * x ^ 4 * u + 6 * x ^ 4 * y
private def cg8_1 (x y u : Rat) : Rat := cg8_1_p0 x y u + cg8_1_p1 x y u
private def cg8_2 (x y u : Rat) : Rat := 63 * u ^ 4 + 102 * y * u ^ 3 + 54 * y ^ 2 * u ^ 2 + 10 * y ^ 3 * u + 132 * x * u ^ 3 + 194 * x * y * u ^ 2 + 80 * x * y ^ 2 * u + 10 * x * y ^ 3 + 84 * x ^ 2 * u ^ 2 + 106 * x ^ 2 * y * u + 26 * x ^ 2 * y ^ 2 + 18 * x ^ 3 * u + 14 * x ^ 3 * y - x ^ 4
private def cg8_3 (x y u : Rat) : Rat := 29 * u ^ 3 + 34 * y * u ^ 2 + 11 * y ^ 2 * u + 51 * x * u ^ 2 + 50 * x * y * u + 11 * x * y ^ 2 + 18 * x ^ 2 * u + 16 * x ^ 2 * y - 4 * x ^ 3
private def cg8_4 (x y u : Rat) : Rat := 7 * u ^ 2 + 7 * y * u + 9 * x * u + 7 * x * y - 6 * x ^ 2
private def cg8_5 (x y u : Rat) : Rat := 2 * u - 4 * x
private def cg8_6 (x y u : Rat) : Rat := -1
private def cg9_0_p0 (x y u : Rat) : Rat := 31 * u ^ 6 + 80 * y * u ^ 5 + 80 * y ^ 2 * u ^ 4 + 40 * y ^ 3 * u ^ 3 + 10 * y ^ 4 * u ^ 2 + y ^ 5 * u + 94 * x * u ^ 5 + 226 * x * y * u ^ 4 + 194 * x * y ^ 2 * u ^ 3 + 79 * x * y ^ 3 * u ^ 2 + 15 * x * y ^ 4 * u + x * y ^ 5 + 100 * x ^ 2 * u ^ 4 + 232 * x ^ 2 * y * u ^ 3
private def cg9_0_p1 (x y u : Rat) : Rat := 164 * x ^ 2 * y ^ 2 * u ^ 2 + 48 * x ^ 2 * y ^ 3 * u + 5 * x ^ 2 * y ^ 4 + 44 * x ^ 3 * u ^ 3 + 102 * x ^ 3 * y * u ^ 2 + 56 * x ^ 3 * y ^ 2 * u + 9 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 17 * x ^ 4 * y * u + 6 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg9_0 (x y u : Rat) : Rat := cg9_0_p0 x y u + cg9_0_p1 x y u
private def cg9_1_p0 (x y u : Rat) : Rat := 69 * u ^ 5 + 146 * y * u ^ 4 + 114 * y ^ 2 * u ^ 3 + 39 * y ^ 3 * u ^ 2 + 5 * y ^ 4 * u + 181 * x * u ^ 4 + 338 * x * y * u ^ 3 + 220 * x * y ^ 2 * u ^ 2 + 58 * x * y ^ 3 * u + 5 * x * y ^ 4 + 165 * x ^ 2 * u ^ 3 + 268 * x ^ 2 * y * u ^ 2 + 129 * x ^ 2 * y ^ 2 * u + 19 * x ^ 2 * y ^ 3
private def cg9_1_p1 (x y u : Rat) : Rat := 59 * x ^ 3 * u ^ 2 + 83 * x ^ 3 * y * u + 23 * x ^ 3 * y ^ 2 + 10 * x ^ 4 * u + 7 * x ^ 4 * y
private def cg9_1 (x y u : Rat) : Rat := cg9_1_p0 x y u + cg9_1_p1 x y u
private def cg9_2 (x y u : Rat) : Rat := 66 * u ^ 4 + 106 * y * u ^ 3 + 56 * y ^ 2 * u ^ 2 + 10 * y ^ 3 * u + 148 * x * u ^ 3 + 204 * x * y * u ^ 2 + 84 * x * y ^ 2 * u + 10 * x * y ^ 3 + 111 * x ^ 2 * u ^ 2 + 117 * x ^ 2 * y * u + 28 * x ^ 2 * y ^ 2 + 30 * x ^ 3 * u + 19 * x ^ 3 * y - x ^ 4
private def cg9_3 (x y u : Rat) : Rat := 34 * u ^ 3 + 38 * y * u ^ 2 + 11 * y ^ 2 * u + 66 * x * u ^ 2 + 58 * x * y * u + 11 * x * y ^ 2 + 36 * x ^ 2 * u + 20 * x ^ 2 * y - 4 * x ^ 3
private def cg9_4 (x y u : Rat) : Rat := 11 * u ^ 2 + 7 * y * u + 17 * x * u + 7 * x * y - 6 * x ^ 2
private def cg9_5 (x y u : Rat) : Rat := 2 * u - 4 * x
private def cg9_6 (x y u : Rat) : Rat := -1
private def cg10_0_p0 (x y u : Rat) : Rat := -8 * u ^ 6 - 8 * y * u ^ 5 - 2 * y ^ 2 * u ^ 4 - 42 * x * u ^ 5 - 45 * x * y * u ^ 4 - 14 * x * y ^ 2 * u ^ 3 - x * y ^ 3 * u ^ 2 - 84 * x ^ 2 * u ^ 4 - 88 * x ^ 2 * y * u ^ 3 - 27 * x ^ 2 * y ^ 2 * u ^ 2 - 2 * x ^ 2 * y ^ 3 * u - 82 * x ^ 3 * u ^ 3 - 77 * x ^ 3 * y * u ^ 2 - 20 * x ^ 3 * y ^ 2 * u
private def cg10_0_p1 (x y u : Rat) : Rat := -x ^ 3 * y ^ 3 - 41 * x ^ 4 * u ^ 2 - 30 * x ^ 4 * y * u - 5 * x ^ 4 * y ^ 2 - 10 * x ^ 5 * u - 4 * x ^ 5 * y - x ^ 6
private def cg10_0 (x y u : Rat) : Rat := cg10_0_p0 x y u + cg10_0_p1 x y u
private def cg10_1_p0 (x y u : Rat) : Rat := -20 * u ^ 5 - 18 * y * u ^ 4 - 6 * y ^ 2 * u ^ 3 - y ^ 3 * u ^ 2 - 104 * x * u ^ 4 - 88 * x * y * u ^ 3 - 22 * x * y ^ 2 * u ^ 2 - 2 * x * y ^ 3 * u - 182 * x ^ 2 * u ^ 3 - 139 * x ^ 2 * y * u ^ 2 - 26 * x ^ 2 * y ^ 2 * u - x ^ 2 * y ^ 3 - 138 * x ^ 3 * u ^ 2 - 86 * x ^ 3 * y * u
private def cg10_1_p1 (x y u : Rat) : Rat := -10 * x ^ 3 * y ^ 2 - 46 * x ^ 4 * u - 17 * x ^ 4 * y - 6 * x ^ 5
private def cg10_1 (x y u : Rat) : Rat := cg10_1_p0 x y u + cg10_1_p1 x y u
private def cg10_2 (x y u : Rat) : Rat := -29 * u ^ 4 - 24 * y * u ^ 3 - 6 * y ^ 2 * u ^ 2 - 116 * x * u ^ 3 - 72 * x * y * u ^ 2 - 12 * x * y ^ 2 * u - 156 * x ^ 2 * u ^ 2 - 72 * x ^ 2 * y * u - 6 * x ^ 2 * y ^ 2 - 80 * x ^ 3 * u - 24 * x ^ 3 * y - 15 * x ^ 4
private def cg10_3 (x y u : Rat) : Rat := -20 * u ^ 3 - 10 * y * u ^ 2 - 60 * x * u ^ 2 - 20 * x * y * u - 60 * x ^ 2 * u - 10 * x ^ 2 * y - 20 * x ^ 3
private def cg10_4 (x y u : Rat) : Rat := -7 * u ^ 2 - 14 * x * u - 15 * x ^ 2
private def cg10_5 (x y u : Rat) : Rat := -6 * x
private def cg10_6 (x y u : Rat) : Rat := -1
private def cg11_0_p0 (x y u : Rat) : Rat := 8 * u ^ 6 + 16 * y * u ^ 5 + 10 * y ^ 2 * u ^ 4 + 2 * y ^ 3 * u ^ 3 + 34 * x * u ^ 5 + 71 * x * y * u ^ 4 + 49 * x * y ^ 2 * u ^ 3 + 13 * x * y ^ 3 * u ^ 2 + x * y ^ 4 * u + 50 * x ^ 2 * u ^ 4 + 101 * x ^ 2 * y * u ^ 3 + 66 * x ^ 2 * y ^ 2 * u ^ 2 + 16 * x ^ 2 * y ^ 3 * u + x ^ 2 * y ^ 4
private def cg11_0_p1 (x y u : Rat) : Rat := 32 * x ^ 3 * u ^ 3 + 58 * x ^ 3 * y * u ^ 2 + 31 * x ^ 3 * y ^ 2 * u + 5 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 13 * x ^ 4 * y * u + 4 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg11_0 (x y u : Rat) : Rat := cg11_0_p0 x y u + cg11_0_p1 x y u
private def cg11_1_p0 (x y u : Rat) : Rat := 28 * u ^ 5 + 46 * y * u ^ 4 + 26 * y ^ 2 * u ^ 3 + 7 * y ^ 3 * u ^ 2 + y ^ 4 * u + 92 * x * u ^ 4 + 154 * x * y * u ^ 3 + 80 * x * y ^ 2 * u ^ 2 + 15 * x * y ^ 3 * u + x * y ^ 4 + 98 * x ^ 2 * u ^ 3 + 159 * x ^ 2 * y * u ^ 2 + 71 * x ^ 2 * y ^ 2 * u + 8 * x ^ 2 * y ^ 3
private def cg11_1_p1 (x y u : Rat) : Rat := 40 * x ^ 3 * u ^ 2 + 57 * x ^ 3 * y * u + 17 * x ^ 3 * y ^ 2 + 6 * x ^ 4 * u + 6 * x ^ 4 * y
private def cg11_1 (x y u : Rat) : Rat := cg11_1_p0 x y u + cg11_1_p1 x y u
private def cg11_2 (x y u : Rat) : Rat := 31 * u ^ 4 + 46 * y * u ^ 3 + 24 * y ^ 2 * u ^ 2 + 5 * y ^ 3 * u + 81 * x * u ^ 3 + 114 * x * y * u ^ 2 + 42 * x * y ^ 2 * u + 5 * x * y ^ 3 + 61 * x ^ 2 * u ^ 2 + 83 * x ^ 2 * y * u + 18 * x ^ 2 * y ^ 2 + 15 * x ^ 3 * u + 15 * x ^ 3 * y
private def cg11_3 (x y u : Rat) : Rat := 20 * u ^ 3 + 26 * y * u ^ 2 + 9 * y ^ 2 * u + 42 * x * u ^ 2 + 43 * x * y * u + 9 * x * y ^ 2 + 22 * x ^ 2 * u + 17 * x ^ 2 * y
private def cg11_4 (x y u : Rat) : Rat := 9 * u ^ 2 + 8 * y * u + 16 * x * u + 8 * x * y - x ^ 2
private def cg11_5 (x y u : Rat) : Rat := 4 * u - 2 * x
private def cg11_6 (x y u : Rat) : Rat := -1
private def cg12_0_p0 (x y u : Rat) : Rat := 15 * u ^ 6 + 24 * y * u ^ 5 + 12 * y ^ 2 * u ^ 4 + 2 * y ^ 3 * u ^ 3 + 53 * x * u ^ 5 + 82 * x * y * u ^ 4 + 36 * x * y ^ 2 * u ^ 3 + 5 * x * y ^ 3 * u ^ 2 + 69 * x ^ 2 * u ^ 4 + 111 * x ^ 2 * y * u ^ 3 + 44 * x ^ 2 * y ^ 2 * u ^ 2 + 5 * x ^ 2 * y ^ 3 * u + 38 * x ^ 3 * u ^ 3 + 67 * x ^ 3 * y * u ^ 2
private def cg12_0_p1 (x y u : Rat) : Rat := 24 * x ^ 3 * y ^ 2 * u + 2 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 15 * x ^ 4 * y * u + 4 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg12_0 (x y u : Rat) : Rat := cg12_0_p0 x y u + cg12_0_p1 x y u
private def cg12_1 (x y u : Rat) : Rat := 18 * u ^ 5 + 14 * y * u ^ 4 + y ^ 2 * u ^ 3 - y ^ 3 * u ^ 2 + 66 * x * u ^ 4 + 56 * x * y * u ^ 3 + 13 * x * y ^ 2 * u ^ 2 + 82 * x ^ 2 * u ^ 3 + 74 * x ^ 2 * y * u ^ 2 + 19 * x ^ 2 * y ^ 2 * u + x ^ 2 * y ^ 3 + 38 * x ^ 3 * u ^ 2 + 37 * x ^ 3 * y * u + 7 * x ^ 3 * y ^ 2 + 8 * x ^ 4 * u + 5 * x ^ 4 * y
private def cg12_2 (x y u : Rat) : Rat := 6 * u ^ 4 + 4 * y * u ^ 3 + 2 * y ^ 2 * u ^ 2 + y ^ 3 * u + 24 * x * u ^ 3 + 22 * x * y * u ^ 2 + 7 * x * y ^ 2 * u + x * y ^ 3 + 33 * x ^ 2 * u ^ 2 + 26 * x ^ 2 * y * u + 5 * x ^ 2 * y ^ 2 + 16 * x ^ 3 * u + 8 * x ^ 3 * y - x ^ 4
private def cg12_3 (x y u : Rat) : Rat := 4 * u ^ 3 + 6 * y * u ^ 2 + 3 * y ^ 2 * u + 18 * x * u ^ 2 + 15 * x * y * u + 3 * x * y ^ 2 + 18 * x ^ 2 * u + 9 * x ^ 2 * y - 4 * x ^ 3
private def cg12_4 (x y u : Rat) : Rat := 5 * u ^ 2 + 4 * y * u + 11 * x * u + 4 * x * y - 6 * x ^ 2
private def cg12_5 (x y u : Rat) : Rat := 2 * u - 4 * x
private def cg12_6 (x y u : Rat) : Rat := -1
private def cg13_0_p0 (x y u : Rat) : Rat := 3 * u ^ 6 + 2 * y * u ^ 5 + 25 * x * u ^ 5 + 36 * x * y * u ^ 4 + 20 * x * y ^ 2 * u ^ 3 + 7 * x * y ^ 3 * u ^ 2 + x * y ^ 4 * u + 47 * x ^ 2 * u ^ 4 + 76 * x ^ 2 * y * u ^ 3 + 38 * x ^ 2 * y ^ 2 * u ^ 2 + 10 * x ^ 2 * y ^ 3 * u + x ^ 2 * y ^ 4 + 32 * x ^ 3 * u ^ 3 + 54 * x ^ 3 * y * u ^ 2
private def cg13_0_p1 (x y u : Rat) : Rat := 21 * x ^ 3 * y ^ 2 * u + 3 * x ^ 3 * y ^ 3 + 9 * x ^ 4 * u ^ 2 + 13 * x ^ 4 * y * u + 3 * x ^ 4 * y ^ 2 + x ^ 5 * u + x ^ 5 * y
private def cg13_0 (x y u : Rat) : Rat := cg13_0_p0 x y u + cg13_0_p1 x y u
private def cg13_1_p0 (x y u : Rat) : Rat := 14 * u ^ 5 + 26 * y * u ^ 4 + 20 * y ^ 2 * u ^ 3 + 7 * y ^ 3 * u ^ 2 + y ^ 4 * u + 62 * x * u ^ 4 + 96 * x * y * u ^ 3 + 58 * x * y ^ 2 * u ^ 2 + 14 * x * y ^ 3 * u + x * y ^ 4 + 82 * x ^ 2 * u ^ 3 + 110 * x ^ 2 * y * u ^ 2 + 49 * x ^ 2 * y ^ 2 * u + 7 * x ^ 2 * y ^ 3
private def cg13_1_p1 (x y u : Rat) : Rat := 36 * x ^ 3 * u ^ 2 + 44 * x ^ 3 * y * u + 11 * x ^ 3 * y ^ 2 + 6 * x ^ 4 * u + 4 * x ^ 4 * y
private def cg13_1 (x y u : Rat) : Rat := cg13_1_p0 x y u + cg13_1_p1 x y u
private def cg13_2 (x y u : Rat) : Rat := 24 * u ^ 4 + 37 * y * u ^ 3 + 20 * y ^ 2 * u ^ 2 + 4 * y ^ 3 * u + 64 * x * u ^ 3 + 85 * x * y * u ^ 2 + 34 * x * y ^ 2 * u + 4 * x * y ^ 3 + 53 * x ^ 2 * u ^ 2 + 57 * x ^ 2 * y * u + 14 * x ^ 2 * y ^ 2 + 14 * x ^ 3 * u + 9 * x ^ 3 * y - x ^ 4
private def cg13_3 (x y u : Rat) : Rat := 15 * u ^ 3 + 18 * y * u ^ 2 + 6 * y ^ 2 * u + 29 * x * u ^ 2 + 28 * x * y * u + 6 * x * y ^ 2 + 18 * x ^ 2 * u + 10 * x ^ 2 * y - 4 * x ^ 3
private def cg13_4 (x y u : Rat) : Rat := 5 * u ^ 2 + 4 * y * u + 11 * x * u + 4 * x * y - 6 * x ^ 2
private def cg13_5 (x y u : Rat) : Rat := 2 * u - 4 * x
private def cg13_6 (x y u : Rat) : Rat := -1
private def cg14_0_p0 (x y u : Rat) : Rat := -u ^ 6 - 18 * x * u ^ 5 - 14 * x * y * u ^ 4 - 6 * x * y ^ 2 * u ^ 3 - x * y ^ 3 * u ^ 2 - 60 * x ^ 2 * u ^ 4 - 48 * x ^ 2 * y * u ^ 3 - 16 * x ^ 2 * y ^ 2 * u ^ 2 - 2 * x ^ 2 * y ^ 3 * u - 76 * x ^ 3 * u ^ 3 - 58 * x ^ 3 * y * u ^ 2 - 14 * x ^ 3 * y ^ 2 * u - x ^ 3 * y ^ 3 - 41 * x ^ 4 * u ^ 2
private def cg14_0_p1 (x y u : Rat) : Rat := -28 * x ^ 4 * y * u - 4 * x ^ 4 * y ^ 2 - 10 * x ^ 5 * u - 4 * x ^ 5 * y - x ^ 6
private def cg14_0 (x y u : Rat) : Rat := cg14_0_p0 x y u + cg14_0_p1 x y u
private def cg14_1_p0 (x y u : Rat) : Rat := -12 * u ^ 5 - 14 * y * u ^ 4 - 6 * y ^ 2 * u ^ 3 - y ^ 3 * u ^ 2 - 68 * x * u ^ 4 - 64 * x * y * u ^ 3 - 20 * x * y ^ 2 * u ^ 2 - 2 * x * y ^ 3 * u - 140 * x ^ 2 * u ^ 3 - 102 * x ^ 2 * y * u ^ 2 - 22 * x ^ 2 * y ^ 2 * u - x ^ 2 * y ^ 3 - 126 * x ^ 3 * u ^ 2 - 68 * x ^ 3 * y * u
private def cg14_1_p1 (x y u : Rat) : Rat := -8 * x ^ 3 * y ^ 2 - 44 * x ^ 4 * u - 16 * x ^ 4 * y - 6 * x ^ 5
private def cg14_1 (x y u : Rat) : Rat := cg14_1_p0 x y u + cg14_1_p1 x y u
private def cg14_2 (x y u : Rat) : Rat := -18 * u ^ 4 - 16 * y * u ^ 3 - 4 * y ^ 2 * u ^ 2 - 76 * x * u ^ 3 - 50 * x * y * u ^ 2 - 8 * x * y ^ 2 * u - 111 * x ^ 2 * u ^ 2 - 52 * x ^ 2 * y * u - 4 * x ^ 2 * y ^ 2 - 66 * x ^ 3 * u - 18 * x ^ 3 * y - 15 * x ^ 4
private def cg14_3 (x y u : Rat) : Rat := -12 * u ^ 3 - 6 * y * u ^ 2 - 36 * x * u ^ 2 - 12 * x * y * u - 36 * x ^ 2 * u - 6 * x ^ 2 * y - 20 * x ^ 3
private def cg14_4 (x y u : Rat) : Rat := -3 * u ^ 2 - 6 * x * u - 15 * x ^ 2
private def cg14_5 (x y u : Rat) : Rat := -6 * x
private def cg14_6 (x y u : Rat) : Rat := -1
private def dg8_2 (x y u : Rat) : Rat := 2 * u ^ 4 + y * u ^ 3 + 6 * x * u ^ 3 + 3 * x * y * u ^ 2 + 4 * x ^ 2 * u ^ 2 + 2 * x ^ 2 * y * u
private def dg8_3 (x y u : Rat) : Rat := u ^ 3 + 3 * x * u ^ 2 + 2 * x ^ 2 * u
private def dg9_2 (x y u : Rat) : Rat := 4 * u ^ 4 + 10 * y * u ^ 3 + 6 * y ^ 2 * u ^ 2 + y ^ 3 * u + 4 * x * u ^ 3 + 14 * x * y * u ^ 2 + 8 * x * y ^ 2 * u + x * y ^ 3 + 4 * x ^ 2 * y * u + 2 * x ^ 2 * y ^ 2
private def dg9_3 (x y u : Rat) : Rat := 9 * u ^ 3 + 12 * y * u ^ 2 + 3 * y ^ 2 * u + 9 * x * u ^ 2 + 15 * x * y * u + 3 * x * y ^ 2 + 3 * x ^ 2 * y
private def dg9_4 (x y u : Rat) : Rat := 6 * u ^ 2 + 3 * y * u + 7 * x * u + 3 * x * y + x ^ 2
private def dg9_5 (x y u : Rat) : Rat := 2 * u + 2 * x
private def dg10_0_p0 (x y u : Rat) : Rat := 11 * u ^ 6 + 37 * y * u ^ 5 + 38 * y ^ 2 * u ^ 4 + 15 * y ^ 3 * u ^ 3 + 2 * y ^ 4 * u ^ 2 + 17 * x * u ^ 5 + 66 * x * y * u ^ 4 + 70 * x * y ^ 2 * u ^ 3 + 26 * x * y ^ 3 * u ^ 2 + 3 * x * y ^ 4 * u + 6 * x ^ 2 * u ^ 4 + 31 * x ^ 2 * y * u ^ 3 + 36 * x ^ 2 * y ^ 2 * u ^ 2 + 12 * x ^ 2 * y ^ 3 * u
private def dg10_0_p1 (x y u : Rat) : Rat := x ^ 2 * y ^ 4 + 2 * x ^ 3 * y * u ^ 2 + 4 * x ^ 3 * y ^ 2 * u + x ^ 3 * y ^ 3
private def dg10_0 (x y u : Rat) : Rat := dg10_0_p0 x y u + dg10_0_p1 x y u
private def dg10_1 (x y u : Rat) : Rat := 27 * u ^ 5 + 69 * y * u ^ 4 + 44 * y ^ 2 * u ^ 3 + 8 * y ^ 3 * u ^ 2 + 39 * x * u ^ 4 + 120 * x * y * u ^ 3 + 75 * x * y ^ 2 * u ^ 2 + 12 * x * y ^ 3 * u + 14 * x ^ 2 * u ^ 3 + 56 * x ^ 2 * y * u ^ 2 + 33 * x ^ 2 * y ^ 2 * u + 4 * x ^ 2 * y ^ 3 + 2 * x ^ 3 * u ^ 2 + 5 * x ^ 3 * y * u + 2 * x ^ 3 * y ^ 2
private def dg10_2 (x y u : Rat) : Rat := 34 * u ^ 4 + 49 * y * u ^ 3 + 14 * y ^ 2 * u ^ 2 + 49 * x * u ^ 3 + 79 * x * y * u ^ 2 + 21 * x * y ^ 2 * u + 16 * x ^ 2 * u ^ 2 + 31 * x ^ 2 * y * u + 7 * x ^ 2 * y ^ 2 + x ^ 3 * u + x ^ 3 * y
private def dg10_3 (x y u : Rat) : Rat := 20 * u ^ 3 + 12 * y * u ^ 2 + 24 * x * u ^ 2 + 16 * x * y * u + 4 * x ^ 2 * u + 4 * x ^ 2 * y
private def dg10_4 (x y u : Rat) : Rat := 4 * u ^ 2 + 4 * x * u
private def dg11_0_p0 (x y u : Rat) : Rat := 6 * u ^ 6 + 11 * y * u ^ 5 + 6 * y ^ 2 * u ^ 4 + y ^ 3 * u ^ 3 + 23 * x * u ^ 5 + 55 * x * y * u ^ 4 + 40 * x * y ^ 2 * u ^ 3 + 11 * x * y ^ 3 * u ^ 2 + x * y ^ 4 * u + 23 * x ^ 2 * u ^ 4 + 69 * x ^ 2 * y * u ^ 3 + 54 * x ^ 2 * y ^ 2 * u ^ 2 + 14 * x ^ 2 * y ^ 3 * u + x ^ 2 * y ^ 4
private def dg11_0_p1 (x y u : Rat) : Rat := 6 * x ^ 3 * u ^ 3 + 27 * x ^ 3 * y * u ^ 2 + 22 * x ^ 3 * y ^ 2 * u + 4 * x ^ 3 * y ^ 3 + 2 * x ^ 4 * y * u + 2 * x ^ 4 * y ^ 2
private def dg11_0 (x y u : Rat) : Rat := dg11_0_p0 x y u + dg11_0_p1 x y u
private def dg11_1 (x y u : Rat) : Rat := 15 * u ^ 5 + 16 * y * u ^ 4 + 4 * y ^ 2 * u ^ 3 + 59 * x * u ^ 4 + 88 * x * y * u ^ 3 + 36 * x * y ^ 2 * u ^ 2 + 4 * x * y ^ 3 * u + 58 * x ^ 2 * u ^ 3 + 108 * x ^ 2 * y * u ^ 2 + 45 * x ^ 2 * y ^ 2 * u + 4 * x ^ 2 * y ^ 3 + 16 * x ^ 3 * u ^ 2 + 39 * x ^ 3 * y * u + 13 * x ^ 3 * y ^ 2 + 2 * x ^ 4 * u + 3 * x ^ 4 * y
private def dg11_2 (x y u : Rat) : Rat := 12 * u ^ 4 + 6 * y * u ^ 3 + 57 * x * u ^ 3 + 46 * x * y * u ^ 2 + 7 * x * y ^ 2 * u + 61 * x ^ 2 * u ^ 2 + 55 * x ^ 2 * y * u + 7 * x ^ 2 * y ^ 2 + 17 * x ^ 3 * u + 15 * x ^ 3 * y + x ^ 4
private def dg11_3 (x y u : Rat) : Rat := 3 * u ^ 3 + 25 * x * u ^ 2 + 8 * x * y * u + 26 * x ^ 2 * u + 8 * x ^ 2 * y + 4 * x ^ 3
private def dg11_4 (x y u : Rat) : Rat := 4 * x * u + 4 * x ^ 2
private def dg12_1 (x y u : Rat) : Rat := 5 * u ^ 5 + 20 * y * u ^ 4 + 21 * y ^ 2 * u ^ 3 + 8 * y ^ 3 * u ^ 2 + y ^ 4 * u + 5 * x * u ^ 4 + 30 * x * y * u ^ 3 + 33 * x * y ^ 2 * u ^ 2 + 11 * x * y ^ 3 * u + x * y ^ 4 + 10 * x ^ 2 * y * u ^ 2 + 13 * x ^ 2 * y ^ 2 * u + 3 * x ^ 2 * y ^ 3 + x ^ 3 * y ^ 2
private def dg12_2 (x y u : Rat) : Rat := 16 * u ^ 4 + 40 * y * u ^ 3 + 24 * y ^ 2 * u ^ 2 + 4 * y ^ 3 * u + 19 * x * u ^ 3 + 60 * x * y * u ^ 2 + 33 * x * y ^ 2 * u + 4 * x * y ^ 3 + 3 * x ^ 2 * u ^ 2 + 21 * x ^ 2 * y * u + 9 * x ^ 2 * y ^ 2 + x ^ 3 * y
private def dg12_3 (x y u : Rat) : Rat := 22 * u ^ 3 + 28 * y * u ^ 2 + 7 * y ^ 2 * u + 28 * x * u ^ 2 + 37 * x * y * u + 7 * x * y ^ 2 + 6 * x ^ 2 * u + 9 * x ^ 2 * y
private def dg12_4 (x y u : Rat) : Rat := 12 * u ^ 2 + 6 * y * u + 13 * x * u + 6 * x * y + x ^ 2
private def dg12_5 (x y u : Rat) : Rat := 2 * u + 2 * x
private def dg13_0_p0 (x y u : Rat) : Rat := 6 * u ^ 6 + 35 * y * u ^ 5 + 56 * y ^ 2 * u ^ 4 + 36 * y ^ 3 * u ^ 3 + 10 * y ^ 4 * u ^ 2 + y ^ 5 * u + 6 * x * u ^ 5 + 55 * x * y * u ^ 4 + 98 * x * y ^ 2 * u ^ 3 + 60 * x * y ^ 3 * u ^ 2 + 14 * x * y ^ 4 * u + x * y ^ 5 + 20 * x ^ 2 * y * u ^ 3 + 48 * x ^ 2 * y ^ 2 * u ^ 2
private def dg13_0_p1 (x y u : Rat) : Rat := 27 * x ^ 2 * y ^ 3 * u + 4 * x ^ 2 * y ^ 4 + 6 * x ^ 3 * y ^ 2 * u + 3 * x ^ 3 * y ^ 3
private def dg13_0 (x y u : Rat) : Rat := dg13_0_p0 x y u + dg13_0_p1 x y u
private def dg13_1 (x y u : Rat) : Rat := 28 * u ^ 5 + 104 * y * u ^ 4 + 106 * y ^ 2 * u ^ 3 + 40 * y ^ 3 * u ^ 2 + 5 * y ^ 4 * u + 34 * x * u ^ 4 + 163 * x * y * u ^ 3 + 168 * x * y ^ 2 * u ^ 2 + 55 * x * y ^ 3 * u + 5 * x * y ^ 4 + 6 * x ^ 2 * u ^ 3 + 61 * x ^ 2 * y * u ^ 2 + 67 * x ^ 2 * y ^ 2 * u + 15 * x ^ 2 * y ^ 3 + 2 * x ^ 3 * y * u + 5 * x ^ 3 * y ^ 2
private def dg13_2 (x y u : Rat) : Rat := 46 * u ^ 4 + 103 * y * u ^ 3 + 60 * y ^ 2 * u ^ 2 + 10 * y ^ 3 * u + 57 * x * u ^ 3 + 149 * x * y * u ^ 2 + 80 * x * y ^ 2 * u + 10 * x * y ^ 3 + 11 * x ^ 2 * u ^ 2 + 47 * x ^ 2 * y * u + 20 * x ^ 2 * y ^ 2 + x ^ 3 * y
private def dg13_3 (x y u : Rat) : Rat := 32 * u ^ 3 + 40 * y * u ^ 2 + 10 * y ^ 2 * u + 38 * x * u ^ 2 + 51 * x * y * u + 10 * x * y ^ 2 + 6 * x ^ 2 * u + 11 * x ^ 2 * y
private def dg13_4 (x y u : Rat) : Rat := 12 * u ^ 2 + 6 * y * u + 13 * x * u + 6 * x * y + x ^ 2
private def dg13_5 (x y u : Rat) : Rat := 2 * u + 2 * x
private def dg14_0 (x y u : Rat) : Rat := u ^ 6 + 21 * y * u ^ 5 + 70 * y ^ 2 * u ^ 4 + 84 * y ^ 3 * u ^ 3 + 45 * y ^ 4 * u ^ 2 + 11 * y ^ 5 * u + y ^ 6 + 15 * x * y * u ^ 4 + 70 * x * y ^ 2 * u ^ 3 + 84 * x * y ^ 3 * u ^ 2 + 36 * x * y ^ 4 * u + 5 * x * y ^ 5 + 15 * x ^ 2 * y ^ 2 * u ^ 2 + 21 * x ^ 2 * y ^ 3 * u + 6 * x ^ 2 * y ^ 4 + x ^ 3 * y ^ 3
private def dg14_1 (x y u : Rat) : Rat := 9 * u ^ 5 + 97 * y * u ^ 4 + 215 * y ^ 2 * u ^ 3 + 169 * y ^ 3 * u ^ 2 + 54 * y ^ 4 * u + 6 * y ^ 5 + 3 * x * u ^ 4 + 71 * x * y * u ^ 3 + 190 * x * y ^ 2 * u ^ 2 + 128 * x * y ^ 3 * u + 24 * x * y ^ 4 + 4 * x ^ 2 * y * u ^ 2 + 36 * x ^ 2 * y ^ 2 * u + 19 * x ^ 2 * y ^ 3 + x ^ 3 * y ^ 2
private def dg14_2 (x y u : Rat) : Rat := 23 * u ^ 4 + 163 * y * u ^ 3 + 229 * y ^ 2 * u ^ 2 + 105 * y ^ 3 * u + 15 * y ^ 4 + 8 * x * u ^ 3 + 111 * x * y * u ^ 2 + 157 * x * y ^ 2 * u + 45 * x * y ^ 3 + 8 * x ^ 2 * y * u + 18 * x ^ 2 * y ^ 2
private def dg14_3 (x y u : Rat) : Rat := 29 * u ^ 3 + 126 * y * u ^ 2 + 100 * y ^ 2 * u + 20 * y ^ 3 + 9 * x * u ^ 2 + 69 * x * y * u + 40 * x * y ^ 2 + 3 * x ^ 2 * y
private def dg14_4 (x y u : Rat) : Rat := 18 * u ^ 2 + 45 * y * u + 15 * y ^ 2 + 3 * x * u + 15 * x * y
private def dg14_5 (x y u : Rat) : Rat := 6 * u + 6 * y
private def dg14_6 (x y u : Rat) : Rat := 1
private theorem cgEq8 (x y z u : Rat) : ck8 x y z u = cg8_0 x y u + z ^ 1 * cg8_1 x y u + z ^ 2 * cg8_2 x y u + z ^ 3 * cg8_3 x y u + z ^ 4 * cg8_4 x y u + z ^ 5 * cg8_5 x y u + z ^ 6 * cg8_6 x y u := by
  simp only [ck8, ck8_p0, ck8_p1, ck8_p2, ck8_p3, ck8_p4, ck8_p5, cg8_0, cg8_0_p0, cg8_0_p1, cg8_1, cg8_1_p0, cg8_1_p1, cg8_2, cg8_3, cg8_4, cg8_5, cg8_6]; try ring
private theorem cgEq9 (x y z u : Rat) : ck9 x y z u = cg9_0 x y u + z ^ 1 * cg9_1 x y u + z ^ 2 * cg9_2 x y u + z ^ 3 * cg9_3 x y u + z ^ 4 * cg9_4 x y u + z ^ 5 * cg9_5 x y u + z ^ 6 * cg9_6 x y u := by
  simp only [ck9, ck9_p0, ck9_p1, ck9_p2, ck9_p3, ck9_p4, ck9_p5, cg9_0, cg9_0_p0, cg9_0_p1, cg9_1, cg9_1_p0, cg9_1_p1, cg9_2, cg9_3, cg9_4, cg9_5, cg9_6]; try ring
private theorem cgEq10 (x y z u : Rat) : ck10 x y z u = cg10_0 x y u + z ^ 1 * cg10_1 x y u + z ^ 2 * cg10_2 x y u + z ^ 3 * cg10_3 x y u + z ^ 4 * cg10_4 x y u + z ^ 5 * cg10_5 x y u + z ^ 6 * cg10_6 x y u := by
  simp only [ck10, ck10_p0, ck10_p1, ck10_p2, ck10_p3, ck10_p4, cg10_0, cg10_0_p0, cg10_0_p1, cg10_1, cg10_1_p0, cg10_1_p1, cg10_2, cg10_3, cg10_4, cg10_5, cg10_6]; try ring
private theorem cgEq11 (x y z u : Rat) : ck11 x y z u = cg11_0 x y u + z ^ 1 * cg11_1 x y u + z ^ 2 * cg11_2 x y u + z ^ 3 * cg11_3 x y u + z ^ 4 * cg11_4 x y u + z ^ 5 * cg11_5 x y u + z ^ 6 * cg11_6 x y u := by
  simp only [ck11, ck11_p0, ck11_p1, ck11_p2, ck11_p3, ck11_p4, ck11_p5, cg11_0, cg11_0_p0, cg11_0_p1, cg11_1, cg11_1_p0, cg11_1_p1, cg11_2, cg11_3, cg11_4, cg11_5, cg11_6]; try ring
private theorem cgEq12 (x y z u : Rat) : ck12 x y z u = cg12_0 x y u + z ^ 1 * cg12_1 x y u + z ^ 2 * cg12_2 x y u + z ^ 3 * cg12_3 x y u + z ^ 4 * cg12_4 x y u + z ^ 5 * cg12_5 x y u + z ^ 6 * cg12_6 x y u := by
  simp only [ck12, ck12_p0, ck12_p1, ck12_p2, ck12_p3, ck12_p4, cg12_0, cg12_0_p0, cg12_0_p1, cg12_1, cg12_2, cg12_3, cg12_4, cg12_5, cg12_6]; try ring
private theorem cgEq13 (x y z u : Rat) : ck13 x y z u = cg13_0 x y u + z ^ 1 * cg13_1 x y u + z ^ 2 * cg13_2 x y u + z ^ 3 * cg13_3 x y u + z ^ 4 * cg13_4 x y u + z ^ 5 * cg13_5 x y u + z ^ 6 * cg13_6 x y u := by
  simp only [ck13, ck13_p0, ck13_p1, ck13_p2, ck13_p3, ck13_p4, ck13_p5, cg13_0, cg13_0_p0, cg13_0_p1, cg13_1, cg13_1_p0, cg13_1_p1, cg13_2, cg13_3, cg13_4, cg13_5, cg13_6]; try ring
private theorem cgEq14 (x y z u : Rat) : ck14 x y z u = cg14_0 x y u + z ^ 1 * cg14_1 x y u + z ^ 2 * cg14_2 x y u + z ^ 3 * cg14_3 x y u + z ^ 4 * cg14_4 x y u + z ^ 5 * cg14_5 x y u + z ^ 6 * cg14_6 x y u := by
  simp only [ck14, ck14_p0, ck14_p1, ck14_p2, ck14_p3, ck14_p4, cg14_0, cg14_0_p0, cg14_0_p1, cg14_1, cg14_1_p0, cg14_1_p1, cg14_2, cg14_3, cg14_4, cg14_5, cg14_6]; try ring
private theorem dgEq8 (x y z u : Rat) : wk8 x y z u = z ^ 2 * dg8_2 x y u + z ^ 3 * dg8_3 x y u := by
  simp only [wk8, dg8_2, dg8_3]; try ring
private theorem dgEq9 (x y z u : Rat) : wk9 x y z u = z ^ 2 * dg9_2 x y u + z ^ 3 * dg9_3 x y u + z ^ 4 * dg9_4 x y u + z ^ 5 * dg9_5 x y u := by
  simp only [wk9, wk9_p0, wk9_p1, dg9_2, dg9_3, dg9_4, dg9_5]; try ring
private theorem dgEq10 (x y z u : Rat) : wk10 x y z u = dg10_0 x y u + z ^ 1 * dg10_1 x y u + z ^ 2 * dg10_2 x y u + z ^ 3 * dg10_3 x y u + z ^ 4 * dg10_4 x y u := by
  simp only [wk10, wk10_p0, wk10_p1, wk10_p2, wk10_p3, dg10_0, dg10_0_p0, dg10_0_p1, dg10_1, dg10_2, dg10_3, dg10_4]; try ring
private theorem dgEq11 (x y z u : Rat) : wk11 x y z u = dg11_0 x y u + z ^ 1 * dg11_1 x y u + z ^ 2 * dg11_2 x y u + z ^ 3 * dg11_3 x y u + z ^ 4 * dg11_4 x y u := by
  simp only [wk11, wk11_p0, wk11_p1, wk11_p2, wk11_p3, dg11_0, dg11_0_p0, dg11_0_p1, dg11_1, dg11_2, dg11_3, dg11_4]; try ring
private theorem dgEq12 (x y z u : Rat) : wk12 x y z u = z ^ 1 * dg12_1 x y u + z ^ 2 * dg12_2 x y u + z ^ 3 * dg12_3 x y u + z ^ 4 * dg12_4 x y u + z ^ 5 * dg12_5 x y u := by
  simp only [wk12, wk12_p0, wk12_p1, wk12_p2, dg12_1, dg12_2, dg12_3, dg12_4, dg12_5]; try ring
private theorem dgEq13 (x y z u : Rat) : wk13 x y z u = dg13_0 x y u + z ^ 1 * dg13_1 x y u + z ^ 2 * dg13_2 x y u + z ^ 3 * dg13_3 x y u + z ^ 4 * dg13_4 x y u + z ^ 5 * dg13_5 x y u := by
  simp only [wk13, wk13_p0, wk13_p1, wk13_p2, wk13_p3, wk13_p4, dg13_0, dg13_0_p0, dg13_0_p1, dg13_1, dg13_2, dg13_3, dg13_4, dg13_5]; try ring
private theorem dgEq14 (x y z u : Rat) : wk14 x y z u = dg14_0 x y u + z ^ 1 * dg14_1 x y u + z ^ 2 * dg14_2 x y u + z ^ 3 * dg14_3 x y u + z ^ 4 * dg14_4 x y u + z ^ 5 * dg14_5 x y u + z ^ 6 * dg14_6 x y u := by
  simp only [wk14, wk14_p0, wk14_p1, wk14_p2, wk14_p3, wk14_p4, dg14_0, dg14_1, dg14_2, dg14_3, dg14_4, dg14_5, dg14_6]; try ring
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
/-- Coefficient of `z ^ 0`: 4 products. -/
private theorem gzh0 (x y u : Rat) :
    cg10_0 x y u * dg10_0 x y u + cg11_0 x y u * dg11_0 x y u + cg13_0 x y u * dg13_0 x y u + cg14_0 x y u * dg14_0 x y u = wzDet x y u ^ 6 - dlo0 x y u := by
  simp only [cg10_0, cg10_0_p0, cg10_0_p1, cg11_0, cg11_0_p0, cg11_0_p1, cg13_0, cg13_0_p0, cg13_0_p1, cg14_0, cg14_0_p0, cg14_0_p1, dg10_0, dg10_0_p0, dg10_0_p1, dg11_0, dg11_0_p0, dg11_0_p1, dg13_0, dg13_0_p0, dg13_0_p1, dg14_0, dlo0, dlo0_p0, dlo0_p1, dlo0_p2, dlo0_p3, wzDet]; try ring
/-- Coefficient of `z ^ 1`: 9 products. -/
private theorem gzh1 (x y u : Rat) :
    cg10_0 x y u * dg10_1 x y u + cg10_1 x y u * dg10_0 x y u + cg11_0 x y u * dg11_1 x y u + cg11_1 x y u * dg11_0 x y u + cg12_0 x y u * dg12_1 x y u + cg13_0 x y u * dg13_1 x y u + cg13_1 x y u * dg13_0 x y u + cg14_0 x y u * dg14_1 x y u + cg14_1 x y u * dg14_0 x y u = wzDet x y u ^ 5 * wzR1 x y u - dlo1 x y u := by
  simp only [cg10_0, cg10_0_p0, cg10_0_p1, cg10_1, cg10_1_p0, cg10_1_p1, cg11_0, cg11_0_p0, cg11_0_p1, cg11_1, cg11_1_p0, cg11_1_p1, cg12_0, cg12_0_p0, cg12_0_p1, cg13_0, cg13_0_p0, cg13_0_p1, cg13_1, cg13_1_p0, cg13_1_p1, cg14_0, cg14_0_p0, cg14_0_p1, cg14_1, cg14_1_p0, cg14_1_p1, dg10_0, dg10_0_p0, dg10_0_p1, dg10_1, dg11_0, dg11_0_p0, dg11_0_p1, dg11_1, dg12_1, dg13_0, dg13_0_p0, dg13_0_p1, dg13_1, dg14_0, dg14_1, dlo1, dlo1_p0, dlo1_p1, dlo1_p2, dlo1_p3, dlo1_p4, wzDet, wzR1]; try ring
/-- Coefficient of `z ^ 2`: 16 products. -/
private theorem gzh2 (x y u : Rat) :
    cg8_0 x y u * dg8_2 x y u + cg9_0 x y u * dg9_2 x y u + cg10_0 x y u * dg10_2 x y u + cg10_1 x y u * dg10_1 x y u + cg10_2 x y u * dg10_0 x y u + cg11_0 x y u * dg11_2 x y u + cg11_1 x y u * dg11_1 x y u + cg11_2 x y u * dg11_0 x y u + cg12_0 x y u * dg12_2 x y u + cg12_1 x y u * dg12_1 x y u + cg13_0 x y u * dg13_2 x y u + cg13_1 x y u * dg13_1 x y u + cg13_2 x y u * dg13_0 x y u + cg14_0 x y u * dg14_2 x y u + cg14_1 x y u * dg14_1 x y u + cg14_2 x y u * dg14_0 x y u = wzDet x y u ^ 4 * wzR2 x y u - dlo2 x y u := by
  simp only [cg10_0, cg10_0_p0, cg10_0_p1, cg10_1, cg10_1_p0, cg10_1_p1, cg10_2, cg11_0, cg11_0_p0, cg11_0_p1, cg11_1, cg11_1_p0, cg11_1_p1, cg11_2, cg12_0, cg12_0_p0, cg12_0_p1, cg12_1, cg13_0, cg13_0_p0, cg13_0_p1, cg13_1, cg13_1_p0, cg13_1_p1, cg13_2, cg14_0, cg14_0_p0, cg14_0_p1, cg14_1, cg14_1_p0, cg14_1_p1, cg14_2, cg8_0, cg8_0_p0, cg8_0_p1, cg9_0, cg9_0_p0, cg9_0_p1, dg10_0, dg10_0_p0, dg10_0_p1, dg10_1, dg10_2, dg11_0, dg11_0_p0, dg11_0_p1, dg11_1, dg11_2, dg12_1, dg12_2, dg13_0, dg13_0_p0, dg13_0_p1, dg13_1, dg13_2, dg14_0, dg14_1, dg14_2, dg8_2, dg9_2, dlo2, dlo2_p0, dlo2_p1, dlo2_p2, dlo2_p3, wzDet, wzR2]; try ring
/-- Coefficient of `z ^ 3`: 23 products. -/
private theorem gzh3 (x y u : Rat) :
    cg8_0 x y u * dg8_3 x y u + cg8_1 x y u * dg8_2 x y u + cg9_0 x y u * dg9_3 x y u + cg9_1 x y u * dg9_2 x y u + cg10_0 x y u * dg10_3 x y u + cg10_1 x y u * dg10_2 x y u + cg10_2 x y u * dg10_1 x y u + cg10_3 x y u * dg10_0 x y u + cg11_0 x y u * dg11_3 x y u + cg11_1 x y u * dg11_2 x y u + cg11_2 x y u * dg11_1 x y u + cg11_3 x y u * dg11_0 x y u + cg12_0 x y u * dg12_3 x y u + cg12_1 x y u * dg12_2 x y u + cg12_2 x y u * dg12_1 x y u + cg13_0 x y u * dg13_3 x y u + cg13_1 x y u * dg13_2 x y u + cg13_2 x y u * dg13_1 x y u + cg13_3 x y u * dg13_0 x y u + cg14_0 x y u * dg14_3 x y u + cg14_1 x y u * dg14_2 x y u + cg14_2 x y u * dg14_1 x y u + cg14_3 x y u * dg14_0 x y u = wzDet x y u ^ 3 * wzR3 x y u - dlo3 x y u := by
  simp only [cg10_0, cg10_0_p0, cg10_0_p1, cg10_1, cg10_1_p0, cg10_1_p1, cg10_2, cg10_3, cg11_0, cg11_0_p0, cg11_0_p1, cg11_1, cg11_1_p0, cg11_1_p1, cg11_2, cg11_3, cg12_0, cg12_0_p0, cg12_0_p1, cg12_1, cg12_2, cg13_0, cg13_0_p0, cg13_0_p1, cg13_1, cg13_1_p0, cg13_1_p1, cg13_2, cg13_3, cg14_0, cg14_0_p0, cg14_0_p1, cg14_1, cg14_1_p0, cg14_1_p1, cg14_2, cg14_3, cg8_0, cg8_0_p0, cg8_0_p1, cg8_1, cg8_1_p0, cg8_1_p1, cg9_0, cg9_0_p0, cg9_0_p1, cg9_1, cg9_1_p0, cg9_1_p1, dg10_0, dg10_0_p0, dg10_0_p1, dg10_1, dg10_2, dg10_3, dg11_0, dg11_0_p0, dg11_0_p1, dg11_1, dg11_2, dg11_3, dg12_1, dg12_2, dg12_3, dg13_0, dg13_0_p0, dg13_0_p1, dg13_1, dg13_2, dg13_3, dg14_0, dg14_1, dg14_2, dg14_3, dg8_2, dg8_3, dg9_2, dg9_3, dlo3, dlo3_p0, dlo3_p1, dlo3_p2, dlo3_p3, wzDet, wzR3]; try ring
/-- Coefficient of `z ^ 4`: 29 products. -/
private theorem gzh4 (x y u : Rat) :
    cg8_1 x y u * dg8_3 x y u + cg8_2 x y u * dg8_2 x y u + cg9_0 x y u * dg9_4 x y u + cg9_1 x y u * dg9_3 x y u + cg9_2 x y u * dg9_2 x y u + cg10_0 x y u * dg10_4 x y u + cg10_1 x y u * dg10_3 x y u + cg10_2 x y u * dg10_2 x y u + cg10_3 x y u * dg10_1 x y u + cg10_4 x y u * dg10_0 x y u + cg11_0 x y u * dg11_4 x y u + cg11_1 x y u * dg11_3 x y u + cg11_2 x y u * dg11_2 x y u + cg11_3 x y u * dg11_1 x y u + cg11_4 x y u * dg11_0 x y u + cg12_0 x y u * dg12_4 x y u + cg12_1 x y u * dg12_3 x y u + cg12_2 x y u * dg12_2 x y u + cg12_3 x y u * dg12_1 x y u + cg13_0 x y u * dg13_4 x y u + cg13_1 x y u * dg13_3 x y u + cg13_2 x y u * dg13_2 x y u + cg13_3 x y u * dg13_1 x y u + cg13_4 x y u * dg13_0 x y u + cg14_0 x y u * dg14_4 x y u + cg14_1 x y u * dg14_3 x y u + cg14_2 x y u * dg14_2 x y u + cg14_3 x y u * dg14_1 x y u + cg14_4 x y u * dg14_0 x y u = wzDet x y u ^ 2 * wzR4 x y u - dlo4 x y u := by
  simp only [cg10_0, cg10_0_p0, cg10_0_p1, cg10_1, cg10_1_p0, cg10_1_p1, cg10_2, cg10_3, cg10_4, cg11_0, cg11_0_p0, cg11_0_p1, cg11_1, cg11_1_p0, cg11_1_p1, cg11_2, cg11_3, cg11_4, cg12_0, cg12_0_p0, cg12_0_p1, cg12_1, cg12_2, cg12_3, cg13_0, cg13_0_p0, cg13_0_p1, cg13_1, cg13_1_p0, cg13_1_p1, cg13_2, cg13_3, cg13_4, cg14_0, cg14_0_p0, cg14_0_p1, cg14_1, cg14_1_p0, cg14_1_p1, cg14_2, cg14_3, cg14_4, cg8_1, cg8_1_p0, cg8_1_p1, cg8_2, cg9_0, cg9_0_p0, cg9_0_p1, cg9_1, cg9_1_p0, cg9_1_p1, cg9_2, dg10_0, dg10_0_p0, dg10_0_p1, dg10_1, dg10_2, dg10_3, dg10_4, dg11_0, dg11_0_p0, dg11_0_p1, dg11_1, dg11_2, dg11_3, dg11_4, dg12_1, dg12_2, dg12_3, dg12_4, dg13_0, dg13_0_p0, dg13_0_p1, dg13_1, dg13_2, dg13_3, dg13_4, dg14_0, dg14_1, dg14_2, dg14_3, dg14_4, dg8_2, dg8_3, dg9_2, dg9_3, dg9_4, dlo4, dlo4_p0, dlo4_p1, dlo4_p2, wzDet, wzR4]; try ring
/-- Coefficient of `z ^ 5`: 33 products. -/
private theorem gzh5 (x y u : Rat) :
    cg8_2 x y u * dg8_3 x y u + cg8_3 x y u * dg8_2 x y u + cg9_0 x y u * dg9_5 x y u + cg9_1 x y u * dg9_4 x y u + cg9_2 x y u * dg9_3 x y u + cg9_3 x y u * dg9_2 x y u + cg10_1 x y u * dg10_4 x y u + cg10_2 x y u * dg10_3 x y u + cg10_3 x y u * dg10_2 x y u + cg10_4 x y u * dg10_1 x y u + cg10_5 x y u * dg10_0 x y u + cg11_1 x y u * dg11_4 x y u + cg11_2 x y u * dg11_3 x y u + cg11_3 x y u * dg11_2 x y u + cg11_4 x y u * dg11_1 x y u + cg11_5 x y u * dg11_0 x y u + cg12_0 x y u * dg12_5 x y u + cg12_1 x y u * dg12_4 x y u + cg12_2 x y u * dg12_3 x y u + cg12_3 x y u * dg12_2 x y u + cg12_4 x y u * dg12_1 x y u + cg13_0 x y u * dg13_5 x y u + cg13_1 x y u * dg13_4 x y u + cg13_2 x y u * dg13_3 x y u + cg13_3 x y u * dg13_2 x y u + cg13_4 x y u * dg13_1 x y u + cg13_5 x y u * dg13_0 x y u + cg14_0 x y u * dg14_5 x y u + cg14_1 x y u * dg14_4 x y u + cg14_2 x y u * dg14_3 x y u + cg14_3 x y u * dg14_2 x y u + cg14_4 x y u * dg14_1 x y u + cg14_5 x y u * dg14_0 x y u = wzDet x y u ^ 1 * wzR5 x y u - dlo5 x y u := by
  simp only [cg10_1, cg10_1_p0, cg10_1_p1, cg10_2, cg10_3, cg10_4, cg10_5, cg11_1, cg11_1_p0, cg11_1_p1, cg11_2, cg11_3, cg11_4, cg11_5, cg12_0, cg12_0_p0, cg12_0_p1, cg12_1, cg12_2, cg12_3, cg12_4, cg13_0, cg13_0_p0, cg13_0_p1, cg13_1, cg13_1_p0, cg13_1_p1, cg13_2, cg13_3, cg13_4, cg13_5, cg14_0, cg14_0_p0, cg14_0_p1, cg14_1, cg14_1_p0, cg14_1_p1, cg14_2, cg14_3, cg14_4, cg14_5, cg8_2, cg8_3, cg9_0, cg9_0_p0, cg9_0_p1, cg9_1, cg9_1_p0, cg9_1_p1, cg9_2, cg9_3, dg10_0, dg10_0_p0, dg10_0_p1, dg10_1, dg10_2, dg10_3, dg10_4, dg11_0, dg11_0_p0, dg11_0_p1, dg11_1, dg11_2, dg11_3, dg11_4, dg12_1, dg12_2, dg12_3, dg12_4, dg12_5, dg13_0, dg13_0_p0, dg13_0_p1, dg13_1, dg13_2, dg13_3, dg13_4, dg13_5, dg14_0, dg14_1, dg14_2, dg14_3, dg14_4, dg14_5, dg8_2, dg8_3, dg9_2, dg9_3, dg9_4, dg9_5, dlo5, dlo5_p0, dlo5_p1, wzDet, wzR5]; try ring
/-- Coefficient of `z ^ 6`: 34 products. -/
private theorem gzh6 (x y u : Rat) :
    cg8_3 x y u * dg8_3 x y u + cg8_4 x y u * dg8_2 x y u + cg9_1 x y u * dg9_5 x y u + cg9_2 x y u * dg9_4 x y u + cg9_3 x y u * dg9_3 x y u + cg9_4 x y u * dg9_2 x y u + cg10_2 x y u * dg10_4 x y u + cg10_3 x y u * dg10_3 x y u + cg10_4 x y u * dg10_2 x y u + cg10_5 x y u * dg10_1 x y u + cg10_6 x y u * dg10_0 x y u + cg11_2 x y u * dg11_4 x y u + cg11_3 x y u * dg11_3 x y u + cg11_4 x y u * dg11_2 x y u + cg11_5 x y u * dg11_1 x y u + cg11_6 x y u * dg11_0 x y u + cg12_1 x y u * dg12_5 x y u + cg12_2 x y u * dg12_4 x y u + cg12_3 x y u * dg12_3 x y u + cg12_4 x y u * dg12_2 x y u + cg12_5 x y u * dg12_1 x y u + cg13_1 x y u * dg13_5 x y u + cg13_2 x y u * dg13_4 x y u + cg13_3 x y u * dg13_3 x y u + cg13_4 x y u * dg13_2 x y u + cg13_5 x y u * dg13_1 x y u + cg13_6 x y u * dg13_0 x y u + cg14_0 x y u * dg14_6 x y u + cg14_1 x y u * dg14_5 x y u + cg14_2 x y u * dg14_4 x y u + cg14_3 x y u * dg14_3 x y u + cg14_4 x y u * dg14_2 x y u + cg14_5 x y u * dg14_1 x y u + cg14_6 x y u * dg14_0 x y u = wzDet x y u ^ 0 * wzR6 x y u - dlo6 x y u := by
  simp only [cg10_2, cg10_3, cg10_4, cg10_5, cg10_6, cg11_2, cg11_3, cg11_4, cg11_5, cg11_6, cg12_1, cg12_2, cg12_3, cg12_4, cg12_5, cg13_1, cg13_1_p0, cg13_1_p1, cg13_2, cg13_3, cg13_4, cg13_5, cg13_6, cg14_0, cg14_0_p0, cg14_0_p1, cg14_1, cg14_1_p0, cg14_1_p1, cg14_2, cg14_3, cg14_4, cg14_5, cg14_6, cg8_3, cg8_4, cg9_1, cg9_1_p0, cg9_1_p1, cg9_2, cg9_3, cg9_4, dg10_0, dg10_0_p0, dg10_0_p1, dg10_1, dg10_2, dg10_3, dg10_4, dg11_0, dg11_0_p0, dg11_0_p1, dg11_1, dg11_2, dg11_3, dg11_4, dg12_1, dg12_2, dg12_3, dg12_4, dg12_5, dg13_0, dg13_0_p0, dg13_0_p1, dg13_1, dg13_2, dg13_3, dg13_4, dg13_5, dg14_0, dg14_1, dg14_2, dg14_3, dg14_4, dg14_5, dg14_6, dg8_2, dg8_3, dg9_2, dg9_3, dg9_4, dg9_5, dlo6, dlo6_p0, dlo6_p1, wzDet, wzR6]; try ring
/-- Coefficient of `z ^ 7`: 30 products. -/
private theorem gzh7 (x y u : Rat) :
    cg8_4 x y u * dg8_3 x y u + cg8_5 x y u * dg8_2 x y u + cg9_2 x y u * dg9_5 x y u + cg9_3 x y u * dg9_4 x y u + cg9_4 x y u * dg9_3 x y u + cg9_5 x y u * dg9_2 x y u + cg10_3 x y u * dg10_4 x y u + cg10_4 x y u * dg10_3 x y u + cg10_5 x y u * dg10_2 x y u + cg10_6 x y u * dg10_1 x y u + cg11_3 x y u * dg11_4 x y u + cg11_4 x y u * dg11_3 x y u + cg11_5 x y u * dg11_2 x y u + cg11_6 x y u * dg11_1 x y u + cg12_2 x y u * dg12_5 x y u + cg12_3 x y u * dg12_4 x y u + cg12_4 x y u * dg12_3 x y u + cg12_5 x y u * dg12_2 x y u + cg12_6 x y u * dg12_1 x y u + cg13_2 x y u * dg13_5 x y u + cg13_3 x y u * dg13_4 x y u + cg13_4 x y u * dg13_3 x y u + cg13_5 x y u * dg13_2 x y u + cg13_6 x y u * dg13_1 x y u + cg14_1 x y u * dg14_6 x y u + cg14_2 x y u * dg14_5 x y u + cg14_3 x y u * dg14_4 x y u + cg14_4 x y u * dg14_3 x y u + cg14_5 x y u * dg14_2 x y u + cg14_6 x y u * dg14_1 x y u = wzR7 x y u - dlo7 x y u := by
  simp only [cg10_3, cg10_4, cg10_5, cg10_6, cg11_3, cg11_4, cg11_5, cg11_6, cg12_2, cg12_3, cg12_4, cg12_5, cg12_6, cg13_2, cg13_3, cg13_4, cg13_5, cg13_6, cg14_1, cg14_1_p0, cg14_1_p1, cg14_2, cg14_3, cg14_4, cg14_5, cg14_6, cg8_4, cg8_5, cg9_2, cg9_3, cg9_4, cg9_5, dg10_1, dg10_2, dg10_3, dg10_4, dg11_1, dg11_2, dg11_3, dg11_4, dg12_1, dg12_2, dg12_3, dg12_4, dg12_5, dg13_1, dg13_2, dg13_3, dg13_4, dg13_5, dg14_1, dg14_2, dg14_3, dg14_4, dg14_5, dg14_6, dg8_2, dg8_3, dg9_2, dg9_3, dg9_4, dg9_5, dlo7, dlo7_p0, dlo7_p1, wzR7]; try ring
/-- Coefficient of `z ^ 8`: 25 products. -/
private theorem gzh8 (x y u : Rat) :
    cg8_5 x y u * dg8_3 x y u + cg8_6 x y u * dg8_2 x y u + cg9_3 x y u * dg9_5 x y u + cg9_4 x y u * dg9_4 x y u + cg9_5 x y u * dg9_3 x y u + cg9_6 x y u * dg9_2 x y u + cg10_4 x y u * dg10_4 x y u + cg10_5 x y u * dg10_3 x y u + cg10_6 x y u * dg10_2 x y u + cg11_4 x y u * dg11_4 x y u + cg11_5 x y u * dg11_3 x y u + cg11_6 x y u * dg11_2 x y u + cg12_3 x y u * dg12_5 x y u + cg12_4 x y u * dg12_4 x y u + cg12_5 x y u * dg12_3 x y u + cg12_6 x y u * dg12_2 x y u + cg13_3 x y u * dg13_5 x y u + cg13_4 x y u * dg13_4 x y u + cg13_5 x y u * dg13_3 x y u + cg13_6 x y u * dg13_2 x y u + cg14_2 x y u * dg14_6 x y u + cg14_3 x y u * dg14_5 x y u + cg14_4 x y u * dg14_4 x y u + cg14_5 x y u * dg14_3 x y u + cg14_6 x y u * dg14_2 x y u = wzR8 x y u - dlo8 x y u := by
  simp only [cg10_4, cg10_5, cg10_6, cg11_4, cg11_5, cg11_6, cg12_3, cg12_4, cg12_5, cg12_6, cg13_3, cg13_4, cg13_5, cg13_6, cg14_2, cg14_3, cg14_4, cg14_5, cg14_6, cg8_5, cg8_6, cg9_3, cg9_4, cg9_5, cg9_6, dg10_2, dg10_3, dg10_4, dg11_2, dg11_3, dg11_4, dg12_2, dg12_3, dg12_4, dg12_5, dg13_2, dg13_3, dg13_4, dg13_5, dg14_2, dg14_3, dg14_4, dg14_5, dg14_6, dg8_2, dg8_3, dg9_2, dg9_3, dg9_4, dg9_5, dlo8, wzR8]; try ring
/-- Coefficient of `z ^ 9`: 18 products. -/
private theorem gzh9 (x y u : Rat) :
    cg8_6 x y u * dg8_3 x y u + cg9_4 x y u * dg9_5 x y u + cg9_5 x y u * dg9_4 x y u + cg9_6 x y u * dg9_3 x y u + cg10_5 x y u * dg10_4 x y u + cg10_6 x y u * dg10_3 x y u + cg11_5 x y u * dg11_4 x y u + cg11_6 x y u * dg11_3 x y u + cg12_4 x y u * dg12_5 x y u + cg12_5 x y u * dg12_4 x y u + cg12_6 x y u * dg12_3 x y u + cg13_4 x y u * dg13_5 x y u + cg13_5 x y u * dg13_4 x y u + cg13_6 x y u * dg13_3 x y u + cg14_3 x y u * dg14_6 x y u + cg14_4 x y u * dg14_5 x y u + cg14_5 x y u * dg14_4 x y u + cg14_6 x y u * dg14_3 x y u = wzR9 x y u - dlo9 x y u := by
  simp only [cg10_5, cg10_6, cg11_5, cg11_6, cg12_4, cg12_5, cg12_6, cg13_4, cg13_5, cg13_6, cg14_3, cg14_4, cg14_5, cg14_6, cg8_6, cg9_4, cg9_5, cg9_6, dg10_3, dg10_4, dg11_3, dg11_4, dg12_3, dg12_4, dg12_5, dg13_3, dg13_4, dg13_5, dg14_3, dg14_4, dg14_5, dg14_6, dg8_3, dg9_3, dg9_4, dg9_5, dlo9, wzR9]; try ring
/-- Coefficient of `z ^ 10`: 11 products. -/
private theorem gzh10 (x y u : Rat) :
    cg9_5 x y u * dg9_5 x y u + cg9_6 x y u * dg9_4 x y u + cg10_6 x y u * dg10_4 x y u + cg11_6 x y u * dg11_4 x y u + cg12_5 x y u * dg12_5 x y u + cg12_6 x y u * dg12_4 x y u + cg13_5 x y u * dg13_5 x y u + cg13_6 x y u * dg13_4 x y u + cg14_4 x y u * dg14_6 x y u + cg14_5 x y u * dg14_5 x y u + cg14_6 x y u * dg14_4 x y u = wzR10 x y u - dlo10 x y u := by
  simp only [cg10_6, cg11_6, cg12_5, cg12_6, cg13_5, cg13_6, cg14_4, cg14_5, cg14_6, cg9_5, cg9_6, dg10_4, dg11_4, dg12_4, dg12_5, dg13_4, dg13_5, dg14_4, dg14_5, dg14_6, dg9_4, dg9_5, dlo10, wzR10]; try ring
/-- Coefficient of `z ^ 11`: 5 products. -/
private theorem gzh11 (x y u : Rat) :
    cg9_6 x y u * dg9_5 x y u + cg12_6 x y u * dg12_5 x y u + cg13_6 x y u * dg13_5 x y u + cg14_5 x y u * dg14_6 x y u + cg14_6 x y u * dg14_5 x y u = wzR11 x y u - dlo11 x y u := by
  simp only [cg12_6, cg13_6, cg14_5, cg14_6, cg9_6, dg12_5, dg13_5, dg14_5, dg14_6, dg9_5, dlo11, wzR11]; try ring
/-- Coefficient of `z ^ 12`: 1 products. -/
private theorem gzh12 (x y u : Rat) :
    cg14_6 x y u * dg14_6 x y u = wzR12 x y u - dlo12 x y u := by
  simp only [cg14_6, dg14_6, dlo12, wzR12]; try ring

end BunkbedTMGradedHi

open Bunkbed Bunkbed.Hyper Bunkbed.TM BunkbedTMGradedHi in
/-- **The fifteen class products are the Wierman--Ziff difference polynomial.** -/
theorem solution (x y z u : Rat) :
    ck0 x y z u * wk0 x y z u + ck1 x y z u * wk1 x y z u + ck2 x y z u * wk2 x y z u + ck3 x y z u * wk3 x y z u + ck4 x y z u * wk4 x y z u + ck5 x y z u * wk5 x y z u + ck6 x y z u * wk6 x y z u + ck7 x y z u * wk7 x y z u + ck8 x y z u * wk8 x y z u + ck9 x y z u * wk9 x y z u + ck10 x y z u * wk10 x y z u + ck11 x y z u * wk11 x y z u + ck12 x y z u * wk12 x y z u + ck13 x y z u * wk13 x y z u + ck14 x y z u * wk14 x y z u
      = wzDiffPoly x y z u := by
  have hlo := BunkbedTM.class_products_lo x y z u
  have hhi : ck8 x y z u * wk8 x y z u + ck9 x y z u * wk9 x y z u + ck10 x y z u * wk10 x y z u + ck11 x y z u * wk11 x y z u + ck12 x y z u * wk12 x y z u + ck13 x y z u * wk13 x y z u + ck14 x y z u * wk14 x y z u
      = wzDiffPoly x y z u - wzDlo x y z u := by
    rw [cgEq8, cgEq9, cgEq10, cgEq11, cgEq12, cgEq13, cgEq14]
    rw [dgEq8, dgEq9, dgEq10, dgEq11, dgEq12, dgEq13, dgEq14]
    rw [wzDiffPoly, dloGr]
    linear_combination gzh0 x y u + z ^ 1 * gzh1 x y u + z ^ 2 * gzh2 x y u + z ^ 3 * gzh3 x y u + z ^ 4 * gzh4 x y u + z ^ 5 * gzh5 x y u + z ^ 6 * gzh6 x y u + z ^ 7 * gzh7 x y u + z ^ 8 * gzh8 x y u + z ^ 9 * gzh9 x y u + z ^ 10 * gzh10 x y u + z ^ 11 * gzh11 x y u + z ^ 12 * gzh12 x y u
  linear_combination hlo + hhi

#print axioms solution
