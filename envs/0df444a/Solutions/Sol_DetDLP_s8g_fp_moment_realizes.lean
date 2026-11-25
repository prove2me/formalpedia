-- Prove2me | solution 1 for DetDLP.s8g_fp_moment_realizes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T19:23:06.4118+00:00
-- url     : https://prove2.me/submissions/9403eb92-2c91-44e3-9a57-91e9ac4ae5f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_w3_m5_modmul_r2
import Theorems.Thm_DetDLP_s8g_fp_moment_wired_encoders

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8G.FpMoment
open DetDLP.S8G.FpMoment.Code

/--
Re-sketch of uniform `PolyT` encoders for tag-1 multiplicative moments.

`w3_m5_modmul_r2` (Proved) supplies the modular-multiplication interface; child
`s8g_fp_moment_wired_encoders` returns one Uniform address compiler that simultaneously
realizes every moment count via `FpMoment.Code.make`/`port` and `ofLayout`.
-/
theorem solution (h : S8C.GadgetLaws) :
    ∃ (make port : List Bool → List Bool) (L : ℕ),
      Groundwork.PolyT make ∧ Groundwork.PolyT port ∧
        ∀ (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool),
          T ≤ p → η.length ≤ blockCount (bitLen p) * 2 * bitLen p →
          S8C.Realizes make port L (word p j T η) (bitLen p)
            (value p (blockCount (bitLen p)) T η j) := by
  let mul := w3_m5_modmul_r2
  obtain ⟨a, ha, hR⟩ := s8g_fp_moment_wired_encoders h mul
  exact ⟨make a, port a, 200000, make_poly a ha, port_poly a ha, hR⟩
