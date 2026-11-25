-- Prove2me | solution 1 for DetDLP.w3_fp_native_wire_programs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:56:20.088544+00:00
-- url     : https://prove2.me/submissions/4ee33f9f-1c02-4308-89af-99a0957999d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_w3_fp_separator_btn
import Theorems.Thm_DetDLP_w3_fp_separator_to_polywire

set_option autoImplicit false

open DetDLP

/-- Reduce native fp wire programs to the separator compiler, then to a `PolyT` wire family. -/
theorem solution (mul : w3_modMulInterface) : w3_polyWireFamily w3_fpQueries := by
  have hsep := DetDLP.w3_fp_separator_btn
  exact w3_fp_separator_to_polywire mul hsep