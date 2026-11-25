-- Prove2me | solution 2 for DetDLP.s8g_fp_moment_wired_encoders
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T04:04:31.497239+00:00
-- url     : https://prove2.me/submissions/4722c11a-cc41-44b5-8b6e-5ceff29be4bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_s8g_fp_moment_layout_compiler_witness

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8G.FpMoment
open DetDLP.S8G.FpMoment.Code

/--
One compiler witness supplies a single uniform `a` and, for every moment query, a
layout whose budgets and `make`/`port` equations match `ofLayout`.
-/
theorem solution (h : S8C.GadgetLaws) (mul : w3_modMulInterface) :
    ∃ a : Addresses,
      a.Uniform ∧
        ∀ (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool),
          T ≤ p → η.length ≤ blockCount (bitLen p) * 2 * bitLen p →
          S8C.Realizes (make a) (port a) 200000 (word p j T η) (bitLen p)
            (value p (blockCount (bitLen p)) T η j) := by
  obtain ⟨a, ha, hpack⟩ := s8g_fp_moment_layout_compiler_witness h mul
  refine ⟨a, ha, ?_⟩
  intro p _ j T η hT hη
  obtain ⟨A, test, hg, W, instW, witness, hcard, hedges, hdeg, build, eval⟩ :=
    hpack p j T η hT hη
  haveI : Fintype W := instW
  exact @ofLayout p T _ j η hT hη A test hg (make a) (port a) W instW witness hcard hedges hdeg
    build eval
