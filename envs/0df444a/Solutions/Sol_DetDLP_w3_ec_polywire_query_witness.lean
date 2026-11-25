-- Prove2me | solution 1 for DetDLP.w3_ec_polywire_query_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:45:42.854345+00:00
-- url     : https://prove2.me/submissions/5baafa2a-41e3-4c3a-9b05-bdfcc36510f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Theorems.Thm_DetDLP_w3_ec_polywire_core_packet

set_option autoImplicit false

open DetDLP DetDLP.M3B.ECPolyDefs Groundwork

/--
`w3_ec_polywire_query_witness` packages the combined ec core packet/size/entry
lemma `w3_ec_polywire_core_packet`.
-/
theorem solution (mul : w3_modMulInterface)
    (hcore : ∀ q, w3_ecQueries q →
      ∃ W : w3_WireCore q 100000000, W.desc = q.input ∧ W.S = 100000000 * q.m * q.b) :
    ∃ c : ℕ, 0 < c ∧
      ∀ q, w3_ecQueries q → ∃ W : w3_WireCore q 100000000,
        ecBuild q.input = w3_wirePacket W ∧
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c ∧
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry w)
            (w3_liftTensor W.G W.T v a) := by
  obtain ⟨c, hc, hpacket, hsize, hentry⟩ := DetDLP.w3_ec_polywire_core_packet mul hcore
  refine ⟨c, hc, fun q hq => ?_⟩
  obtain ⟨W, hW⟩ := hpacket q hq
  exact ⟨W, hW, hsize q hq W hW, hentry q hq W hW⟩
