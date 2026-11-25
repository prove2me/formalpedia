-- Prove2me | solution 1 for DetDLP.s8m_ec_pair_realizes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T19:32:43.826506+00:00
-- url     : https://prove2.me/submissions/df9c3753-2ac8-44d6-9d6b-5d300c1c9c3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPacket
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8m_ec_pair_wired_encoders

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8M.ECPair
open DetDLP.S8M.ECPair.Packet

/--
Re-sketch of uniform `PolyT` encoders for tag-6 EC pair queries via a single wired
address compiler (`s8m_ec_pair_wired_encoders`), avoiding the unsound split through
the trivial `s8g_fp_moment_addresses`.
-/
theorem solution (h : S8C.GadgetLaws) :
    ∃ (make port : List Bool → List Bool) (L : ℕ),
      Groundwork.PolyT make ∧ Groundwork.PolyT port ∧
        ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          ∀ (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool),
            T ≤ p → η.length ≤ 2 * blockCount (bitLen p) * (2 * bitLen p + 1) →
              S8C.Realizes make port L (word E T S X η) (bitLen p) (value E T S X η) := by
  obtain ⟨a, ha, hR⟩ := s8m_ec_pair_wired_encoders h
  exact ⟨make a, port a, 1600000, make_poly a ha, port_poly a ha, hR⟩
