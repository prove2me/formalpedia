-- Prove2me | solution 1 for DetDLP.s8m_ec_pair_layout_compiler_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T05:39:01.871132+00:00
-- url     : https://prove2.me/submissions/6e5ae5b5-863b-4958-972d-568c9ab47887
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPacket
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8m_ec_pair_layout_compiler_endpoints

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8M.ECPair
open DetDLP.S8M.ECPair.Packet
open Groundwork
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/--
Package proved address-field uniformity (`Addresses.mk` of the `PolyT` compilers)
and discharge the BTN packet equations by `make_word` / `port_word`.
-/
theorem solution (h : S8C.GadgetLaws) :
    ∃ a : S8G.FpMoment.Code.Addresses, a.Uniform ∧
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          ∀ (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool),
            T ≤ p → η.length ≤ 2 * blockCount (bitLen p) * (2 * bitLen p + 1) →
            ∃ (A : w3_FactorLayout) (test : w3_factorTest A) (hg : Function.Surjective A.gate)
              (W : Type) (instW : Fintype W)
              (witness :
                {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃ W),
              Fintype.card W = value E T S X η ∧
                2 * A.ne < scale (blockCount (bitLen p)) (bitLen p) ∧
                (∀ v, (w3_factorGraph A).deg v ≤
                  max 12 (Nat.ceil (136 * ((bitLen p : ℝ) + 2) ^ ((3 : ℝ) / 4)))) ∧
                make a (word E T S X η) =
                  encodeBTNInstance (word E T S X η) (w3_factorGraph A).subdivision
                    (scale (blockCount (bitLen p)) (bitLen p))
                    (scale (blockCount (bitLen p)) (bitLen p)) 1 ∧
                ∀ v a',
                  port a (encodePortQuery (word E T S X η) v.val (List.ofFn a')) =
                    encodeNatListBin
                      [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a'
                        then 1 else 0] := by
  obtain ⟨nv, ne, src, dst, check, hnv, hne, hvert, hedge, hsrc, hdst, hcheck, hlay⟩ :=
    s8m_ec_pair_layout_compiler_endpoints h
  let a : S8G.FpMoment.Code.Addresses := ⟨nv, ne, src, dst, check⟩
  refine ⟨a, ⟨hnv, hne, hvert, hedge, hsrc, hdst, hcheck⟩, ?_⟩
  intro p _ hp E _ T S X η hT hη
  obtain ⟨A, test, hg, W, instW, witness, hcard, hedges, hdeg, hv, he, hs, hd, hc⟩ :=
    hlay p hp E T S X η hT hη
  haveI : Fintype W := instW
  refine ⟨A, test, hg, W, instW, witness, hcard, hedges, hdeg, ?_, ?_⟩
  · exact make_word E T S X η a (w3_factorGraph A) hv he hs hd
  · intro v a'
    have hc' :
        a.check (word E T S X η, v.val, List.ofFn a') =
          (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a' := by
      simpa [a] using hc v a'
    rw [port_word a (word E T S X η) v.val (List.ofFn a'), hc']
