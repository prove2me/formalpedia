-- Prove2me | solution 1 for DetDLP.s8g_fp_moment_wirekit_compiler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T20:04:28.409288+00:00
-- url     : https://prove2.me/submissions/3bccf5da-b676-4cbd-b9a8-bff4de56c3a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_s8g_fp_moment_wirefamily_to_addresses
import Theorems.Thm_DetDLP_w3_fp_native_wire_programs

set_option autoImplicit false

open DetDLP S8G.FpMoment.Code

theorem solution (h : S8C.GadgetLaws) (mul : w3_modMulInterface) :
    ∃ a : Addresses, a.Uniform := by
  have hwf := w3_fp_native_wire_programs mul
  exact s8g_fp_moment_wirefamily_to_addresses mul hwf