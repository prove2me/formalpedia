-- Prove2me | solution 1 for DetDLP.s8g_fp_moment_point_compiler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T20:13:44.48634+00:00
-- url     : https://prove2.me/submissions/6579c5ab-c18f-4fd3-a4cb-01666e76c385
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_s8g_fp_moment_wirekit_compiler

set_option autoImplicit false

open DetDLP S8G.FpMoment.Code

theorem solution (h : S8C.GadgetLaws) (mul : w3_modMulInterface) :
    ∃ a : Addresses, a.Uniform :=
  s8g_fp_moment_wirekit_compiler h mul