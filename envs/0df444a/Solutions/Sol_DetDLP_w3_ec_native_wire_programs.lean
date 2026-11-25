-- Prove2me | solution 1 for DetDLP.w3_ec_native_wire_programs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:05:24.307468+00:00
-- url     : https://prove2.me/submissions/09c3ca0e-4c6b-4453-b745-481a63683448
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_w3_ec_separator_btn
import Theorems.Thm_DetDLP_w3_ec_separator_to_polywire

set_option autoImplicit false

open DetDLP

/-- Reduce native ec wire programs to the separator compiler, then to a `PolyT` wire family. -/
theorem solution (mul : w3_modMulInterface) : w3_polyWireFamily w3_ecQueries := by
  have hsep := DetDLP.w3_ec_separator_btn
  exact w3_ec_separator_to_polywire mul hsep