-- Prove2me | solution 2 for DetDLP.s8g_fp_moment_layout_semantic_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:29:54.939135+00:00
-- url     : https://prove2.me/submissions/bc2621ad-61b9-432e-9f72-e85955699721
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_s8g_fp_moment_layout_semantic_package

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8G.FpMoment

/-- Project the sound ∃ package onto the witness/cardinality fragment. -/
theorem solution (h : S8C.GadgetLaws) (mul : w3_modMulInterface)
    (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool)
    (hT : T ≤ p) (hη : η.length ≤ blockCount (bitLen p) * 2 * bitLen p) :
    ∃ (A : w3_FactorLayout) (test : w3_factorTest A) (hg : Function.Surjective A.gate)
      (W : Type) (instW : Fintype W)
      (witness :
        {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃ W),
      Fintype.card W = value p (blockCount (bitLen p)) T η j := by
  obtain ⟨A, test, hg, W, instW, witness, hpack⟩ :=
    s8g_fp_moment_layout_semantic_package h mul p j T η hT hη
  exact ⟨A, test, hg, W, instW, witness, hpack.1⟩
