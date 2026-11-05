-- Prove2me | solution 1 for BookProof.TensorSumChain.chain_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T15:23:08.273202+00:00
-- url     : https://prove2.me/submissions/f5ec7a62-0fa2-4c42-b61e-7c0c85609a73

-- Generated from ChapterTensorSumChain.lean — solution of BookProof.TensorSumChain.chain_esa
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TensorSumChain




open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore BookProof.TensorSumEsa

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (E : EsaOp) (L : List EsaOp) :
    EssentiallySelfAdjointOn (chain E L).dom (chain E L).op := (chain E L).esa
