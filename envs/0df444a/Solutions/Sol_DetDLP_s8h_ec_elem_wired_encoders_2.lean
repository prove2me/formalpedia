-- Prove2me | solution 2 for DetDLP.s8h_ec_elem_wired_encoders
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T04:37:24.174205+00:00
-- url     : https://prove2.me/submissions/f21b9d21-b5ee-4b8a-bbfa-a1730c29daac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8H_ECElemGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8h_ec_elem_layout_compiler_witness

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8H.ECElem
open DetDLP.S8G.FpMoment.Code

/-- Uniform `PolyT` encoders are the `make`/`port` maps of one realizing address compiler. -/
theorem solution (h : S8C.GadgetLaws) :
    ∃ (make port : List Bool → List Bool) (L : ℕ),
      Groundwork.PolyT make ∧ Groundwork.PolyT port ∧
        ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          ∀ (T : ℕ) (S : ECSeed p (blockCount (bitLen p)))
            (i : Fin (blockCount (bitLen p))) (η : List Bool),
            T ≤ p → η.length ≤ 2 * bitLen p + 1 →
            S8C.Realizes make port L (word E T S i η) (bitLen p)
              (value E T S i η) := by
  obtain ⟨a, ha, hR⟩ := s8h_ec_elem_layout_compiler_witness h
  exact ⟨make a, port a, 200000, make_poly a ha, port_poly a ha, hR⟩
