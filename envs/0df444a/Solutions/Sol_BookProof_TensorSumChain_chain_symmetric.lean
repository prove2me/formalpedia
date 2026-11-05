-- Prove2me | solution 1 for BookProof.TensorSumChain.chain_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T15:23:13.218567+00:00
-- url     : https://prove2.me/submissions/cbd844b5-48c0-4bc6-aacc-3491aae6d6c2

-- Generated from ChapterTensorSumChain.lean — solution of BookProof.TensorSumChain.chain_symmetric
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
    SymmetricOn (chain E L).dom (chain E L).op := (chain E L).sym
