-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.fpEntry_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:52:30.280865+00:00
-- url     : https://prove2.me/submissions/a31e1cf7-8e09-4feb-8570-a8bc789d8b98

import Definitions.Def_DetDLP_M3A_FpPolyDefs
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_entry_support
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_ordinary_poly
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_lookup_poly
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_compose

set_option autoImplicit false

open DetDLP.M3A.FpPolyDefs Groundwork

/-- Reduce `fpEntry_poly` to compositional PolyT children: field/size extractors,
    ordinary-gate indicator, lookup evaluator, and the packaging compose lemma. -/
theorem solution : PolyT DetDLP.M3A.FpPolyDefs.fpEntry :=
  fpEntry_compose
    (@entry_support (List Bool) _)
    fpEntry_ordinary_poly
    fpEntry_lookup_poly
