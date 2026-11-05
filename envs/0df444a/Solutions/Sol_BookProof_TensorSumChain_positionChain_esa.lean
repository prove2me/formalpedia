-- Prove2me | solution 1 for BookProof.TensorSumChain.positionChain_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T15:35:12.696194+00:00
-- url     : https://prove2.me/submissions/cfb0ab7a-1934-4b66-b9c4-4d311a99539e

-- Generated from ChapterTensorSumChain.lean — solution of BookProof.TensorSumChain.positionChain_esa
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Theorems.Thm_BookProof_TensorSumChain_chain_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TensorSumChain




open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore BookProof.TensorSumEsa

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    EssentiallySelfAdjointOn (chain posEsaOp (List.replicate n posEsaOp)).dom
      (chain posEsaOp (List.replicate n posEsaOp)).op := chain_esa posEsaOp (List.replicate n posEsaOp)
