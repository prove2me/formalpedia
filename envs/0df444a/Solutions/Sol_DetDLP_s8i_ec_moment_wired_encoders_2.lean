-- Prove2me | solution 2 for DetDLP.s8i_ec_moment_wired_encoders
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T04:48:43.391679+00:00
-- url     : https://prove2.me/submissions/654ba2e9-0f1c-457b-b7c2-1f6ede2979e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8I_ECMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8i_ec_moment_layout_compiler_witness

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8I.ECMoment
open DetDLP.S8G.FpMoment.Code

/-- Uniform `PolyT` encoders are the `make`/`port` maps of one realizing address compiler. -/
theorem solution (h : S8C.GadgetLaws) :
    ∃ (make port : List Bool → List Bool) (L : ℕ),
      Groundwork.PolyT make ∧ Groundwork.PolyT port ∧
        ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          ∀ (j : Fin 4) (T : ℕ) (η : List Bool), T ≤ p →
            η.length ≤ blockCount (bitLen p) * 4 * bitLen p →
            S8C.Realizes make port L (word E j T η) (bitLen p)
              (S8I.ECQueryCount.value p (blockCount (bitLen p)) E T η j) := by
  obtain ⟨a, ha, hR⟩ := s8i_ec_moment_layout_compiler_witness h
  exact ⟨make a, port a, 200000, make_poly a ha, port_poly a ha, hR⟩
