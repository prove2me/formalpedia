-- Prove2me | solution 2 for DetDLP.s8i_ec_moment_realizes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T19:55:38.357046+00:00
-- url     : https://prove2.me/submissions/203add8d-5d7e-415c-80bf-a62cf47d8bf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8I_ECMomentGraph
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8i_ec_moment_wired_encoders

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8I.ECMoment

/-- Sketch: tag-2 EC moment realizes reduces to `s8i_ec_moment_wired_encoders`. -/
theorem solution (h : S8C.GadgetLaws) :
    ∃ (make port : List Bool → List Bool) (L : ℕ),
      Groundwork.PolyT make ∧ Groundwork.PolyT port ∧
        ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          ∀ (j : Fin 4) (T : ℕ) (η : List Bool), T ≤ p →
            η.length ≤ blockCount (bitLen p) * 4 * bitLen p →
            S8C.Realizes make port L (word E j T η) (bitLen p)
              (S8I.ECQueryCount.value p (blockCount (bitLen p)) E T η j) := by
  exact s8i_ec_moment_wired_encoders h
