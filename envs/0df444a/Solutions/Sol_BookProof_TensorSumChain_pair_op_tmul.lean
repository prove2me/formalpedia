-- Prove2me | solution 1 for BookProof.TensorSumChain.pair_op_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T19:48:50.683966+00:00
-- url     : https://prove2.me/submissions/01cbb705-a3c3-4d1a-875e-930f7c7abcad

-- Generated from ChapterTensorSumChain.lean — solution of BookProof.TensorSumChain.pair_op_tmul
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
theorem solution (E F : EsaOp) (x : E.dom) (y : F.dom)
    (v : (pair E F).dom)
    (hv : (v : (pair E F).space.carrier)
      = pairEmb E.space F.space (inclPair E.space F.space E.dom F.dom (x ⊗ₜ[ℂ] y))) :
    (pair E F).op v
      = pairEmb E.space F.space
        ((E.op x) ⊗ₜ[ℂ] (y : F.space.carrier) + (x : E.space.carrier) ⊗ₜ[ℂ] (F.op y)) := by

  have h := cpairOp_apply E.space F.space E.dom F.dom E.op F.op v (x ⊗ₜ[ℂ] y) hv
  show cpairOp E.space F.space E.dom F.dom E.op F.op v = _
  simpa [sumPoly_tmul] using h
