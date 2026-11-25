-- Prove2me | solution 1 for DetDLP.w3_fp_polywire_query_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:49:58.721205+00:00
-- url     : https://prove2.me/submissions/e8893e99-b58d-42dc-873a-2d1a23463f6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3A_FpWireCore
import Definitions.Def_DetDLP_M3A_FpPolyDefs
import Theorems.Thm_DetDLP_w3_fp_polywire_core_packet

set_option autoImplicit false

open DetDLP DetDLP.M3A Groundwork

/--
`w3_fp_polywire_query_witness` is the packaging of the combined native-core
packet/size/entry lemma `w3_fp_polywire_core_packet`.
-/
theorem solution (mul : w3_modMulInterface)
    (hcore : FpWireCore.CoreFamily) :
    ∃ c : ℕ, 0 < c ∧
      ∀ q, w3_fpQueries q → ∃ W : w3_WireCore q 1000000,
        FpPolyDefs.fpBuild q.input = w3_wirePacket W ∧
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c ∧
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (FpPolyDefs.fpEntry w)
            (w3_liftTensor W.G W.T v a) := by
  obtain ⟨c, hc, hpacket, hsize, hentry⟩ := DetDLP.w3_fp_polywire_core_packet mul hcore
  refine ⟨c, hc, fun q hq => ?_⟩
  obtain ⟨W, hW⟩ := hpacket q hq
  exact ⟨W, hW, hsize q hq W hW, hentry q hq W hW⟩
