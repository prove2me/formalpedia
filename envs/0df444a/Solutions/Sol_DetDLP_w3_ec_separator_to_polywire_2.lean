-- Prove2me | solution 2 for DetDLP.w3_ec_separator_to_polywire
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:13:06.157003+00:00
-- url     : https://prove2.me/submissions/c823028d-1a3f-4e7e-8fa8-f0ff37d41e66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_W3_Separator
import Theorems.Thm_DetDLP_m3b_ec_wire_core_exists
import Theorems.Thm_DetDLP_w3_ec_polywire_assemble

set_option autoImplicit false

open DetDLP

/-- Ignore the Separator witness: assemble a PolyT wire family from per-query
    ec wire-core existence (`m3b_ec_wire_core_exists`). -/
theorem solution (mul : w3_modMulInterface)
    (hsep : w3_Separator w3_ecQueries) : w3_polyWireFamily w3_ecQueries :=
  w3_ec_polywire_assemble mul DetDLP.m3b_ec_wire_core_exists
