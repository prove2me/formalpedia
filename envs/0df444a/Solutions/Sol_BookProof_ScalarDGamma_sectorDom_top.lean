-- Prove2me | solution 1 for BookProof.ScalarDGamma.sectorDom_top
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:25:21.846004+00:00
-- url     : https://prove2.me/submissions/04e742a4-0e93-4afb-be50-897c0eaec369

-- Generated from ChapterScalarDGammaEsa.lean — solution of BookProof.ScalarDGamma.sectorDom_top
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.ScalarDGamma




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

variable (Hs : IPSpace) (c : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : sectorDom Hs ⊤ n = ⊤ := LinearMap.range_eq_top.mpr (inclPow_top_surjective Hs n)
