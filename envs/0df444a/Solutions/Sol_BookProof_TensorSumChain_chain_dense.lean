-- Prove2me | solution 1 for BookProof.TensorSumChain.chain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T15:23:17.976918+00:00
-- url     : https://prove2.me/submissions/27a1dad8-dbe5-4314-bd55-5b6d98e5a876

-- Generated from ChapterTensorSumChain.lean — solution of BookProof.TensorSumChain.chain_dense
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
open BookProof.TensorSumChain




open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore BookProof.TensorSumEsa

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (E : EsaOp) (L : List EsaOp) :
    Dense (((chain E L).dom : Submodule ℂ (chain E L).space.carrier) :
      Set (chain E L).space.carrier) := (chain E L).dense
