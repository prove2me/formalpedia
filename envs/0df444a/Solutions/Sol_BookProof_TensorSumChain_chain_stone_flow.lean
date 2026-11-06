-- Prove2me | solution 1 for BookProof.TensorSumChain.chain_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:33:32.334591+00:00
-- url     : https://prove2.me/submissions/3bf7942d-ab53-4fdb-b97a-e7e993a6a17d

import Definitions.Def_ChapterTensorSumChain
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa

open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.TensorSumChain
open BookProof.ChapterStoneResolvent

noncomputable section

theorem solution (E : EsaOp) (L : List EsaOp) :
    ∃ (G : UnboundedSelfAdjoint (chain E L).space.carrier)
      (U : ℝ → ((chain E L).space.carrier →L[ℂ] (chain E L).space.carrier)),
      IsSelfAdjointExtension (chain E L).op G.op ∧ IsStoneFlow G U := by
  letI := (chain E L).complete
  exact BookProof.StoneBridge.exists_stone_flow_of_esa
    (chain E L).op (chain E L).dense (chain E L).sym (chain E L).esa
