-- Prove2me | solution 1 for DetDLP.w3_ec_polywire_assemble
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:50:42.284639+00:00
-- url     : https://prove2.me/submissions/a7fcf337-25dd-4698-9c7d-6ea7e94f9fef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Theorems.Thm_DetDLP_m3b_ec_build_poly
import Theorems.Thm_DetDLP_m3b_ec_entry_poly
import Theorems.Thm_DetDLP_w3_ec_polywire_query_witness

set_option autoImplicit false

open DetDLP DetDLP.M3B.ECPolyDefs

/-- Package proved `ecBuild`/`ecEntry` PolyT certificates with the ec query-witness
    lemma into a uniform `w3_polyWireFamily`. -/
theorem solution (mul : w3_modMulInterface)
    (hcore : ∀ q, w3_ecQueries q →
      ∃ W : w3_WireCore q 100000000, W.desc = q.input ∧ W.S = 100000000 * q.m * q.b) :
    w3_polyWireFamily w3_ecQueries := by
  obtain ⟨c, hc, hwit⟩ := DetDLP.w3_ec_polywire_query_witness mul hcore
  refine ⟨100000000, c, ecBuild, ecEntry, by omega, hc, m3b_ec_build_poly, m3b_ec_entry_poly, hwit⟩
