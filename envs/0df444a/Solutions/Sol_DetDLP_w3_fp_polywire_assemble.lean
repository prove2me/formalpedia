-- Prove2me | solution 1 for DetDLP.w3_fp_polywire_assemble
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:37:53.552407+00:00
-- url     : https://prove2.me/submissions/7f043df8-c6ef-4b8d-a94b-e0db994e5cfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3A_FpWireCore
import Definitions.Def_DetDLP_M3A_FpPolyDefs
import Theorems.Thm_DetDLP_w3_fp_polywire_query_witness

set_option autoImplicit false

open DetDLP DetDLP.M3A

/-- Package PolyT certificates with the native fp query-witness lemma into a
    uniform `w3_polyWireFamily`. -/
theorem solution (mul : w3_modMulInterface)
    (hcore : FpWireCore.CoreFamily)
    (hbuild : Groundwork.PolyT FpPolyDefs.fpBuild)
    (hentry : Groundwork.PolyT FpPolyDefs.fpEntry) :
    w3_polyWireFamily w3_fpQueries := by
  obtain ⟨c, hc, hwit⟩ := DetDLP.w3_fp_polywire_query_witness mul hcore
  refine ⟨1000000, c, FpPolyDefs.fpBuild, FpPolyDefs.fpEntry, by omega, hc, hbuild, hentry, hwit⟩
