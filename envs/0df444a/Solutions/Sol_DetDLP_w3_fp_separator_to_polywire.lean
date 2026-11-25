-- Prove2me | solution 1 for DetDLP.w3_fp_separator_to_polywire
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T23:52:40.246209+00:00
-- url     : https://prove2.me/submissions/1afc6f24-426a-49c0-b144-40b76387f354
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_W3_Separator
import Theorems.Thm_DetDLP_M3A_FpWireCore_native_core_family
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpBuild_poly
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_poly
import Theorems.Thm_DetDLP_w3_fp_polywire_assemble

set_option autoImplicit false

open DetDLP DetDLP.M3A

/-- Ignore the Separator witness: assemble a PolyT wire family from the proved
    M3A native core family plus `fpBuild`/`fpEntry` certificates. -/
theorem solution (mul : w3_modMulInterface)
    (hsep : w3_Separator w3_fpQueries) : w3_polyWireFamily w3_fpQueries :=
  w3_fp_polywire_assemble mul
    DetDLP.M3A.FpWireCore.native_core_family
    DetDLP.M3A.FpPolyDefs.fpBuild_poly
    DetDLP.M3A.FpPolyDefs.fpEntry_poly
