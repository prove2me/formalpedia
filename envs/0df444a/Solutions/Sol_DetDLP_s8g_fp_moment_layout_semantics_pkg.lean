-- Prove2me | solution 1 for DetDLP.s8g_fp_moment_layout_semantics_pkg
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T04:44:40.920338+00:00
-- url     : https://prove2.me/submissions/ebbc3e56-b987-4615-8c4d-8c80b8675335
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8G_FpMomentLayoutSemantics
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_s8g_fp_moment_layout_semantic_package

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8G.FpMoment

/-- Sound packaging via ∃ semantic package into the published Def structure. -/
theorem solution (h : S8C.GadgetLaws) (mul : w3_modMulInterface)
    (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool)
    (hT : T ≤ p) (hη : η.length ≤ blockCount (bitLen p) * 2 * bitLen p) :
    Nonempty (FpMomentLayoutSemantics p j T η) := by
  obtain ⟨A, test, hg, W, instW, witness, hpack⟩ :=
    s8g_fp_moment_layout_semantic_package h mul p j T η hT hη
  have : Fintype W := instW
  obtain ⟨count, edges, degree⟩ := hpack
  exact ⟨⟨A, test, hg, W, instW, witness, count, edges, degree⟩⟩
