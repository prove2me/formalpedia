-- Prove2me | solution 3 for DetDLP.s8m_ec_pair_wired_encoders
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T04:04:32.737009+00:00
-- url     : https://prove2.me/submissions/89615e5f-243a-4d69-a65e-19cff406863b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPacket
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8m_ec_pair_layout_compiler_witness

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8M.ECPair
open DetDLP.S8M.ECPair.Packet

/-- Package the single wired compiler into `Realizes` by `ECPair.ofLayout`. -/
theorem solution (h : S8C.GadgetLaws) :
    ∃ a : S8G.FpMoment.Code.Addresses,
      a.Uniform ∧
        ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          ∀ (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool),
            T ≤ p → η.length ≤ 2 * blockCount (bitLen p) * (2 * bitLen p + 1) →
              S8C.Realizes (make a) (port a) 1600000 (word E T S X η) (bitLen p)
                (value E T S X η) := by
  obtain ⟨a, ha, hpack⟩ := s8m_ec_pair_layout_compiler_witness h
  refine ⟨a, ha, ?_⟩
  intro p _ hp E _ T S X η hT hη
  obtain ⟨A, test, hg, W, instW, witness, hcard, hedges, hdeg, build, eval⟩ :=
    hpack p hp E T S X η hT hη
  haveI : Fintype W := instW
  exact @ofLayout p _ E _ T S X η hT hη A test hg (make a) (port a) W instW witness hcard hedges
    hdeg build eval
