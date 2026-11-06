-- Prove2me | solution 1 for BookProof.SmComparisonFull.sm_N_full_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:36:42.998484+00:00
-- url     : https://prove2.me/submissions/75479385-dddb-4025-b033-b1fe188333e5

import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterSmComparisonFull

open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.FarisLavine
open BookProof.ScalaronEsa
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open BookProof.SmComparisonFull
open MeasureTheory

noncomputable section

theorem solution :
    ∃ (G : UnboundedSelfAdjoint smFullChain.space.carrier)
      (U : ℝ → (smFullChain.space.carrier →L[ℂ] smFullChain.space.carrier)),
      IsSelfAdjointExtension smFullChain.op G.op ∧ IsStoneFlow G U := by
  letI := smFullChain.complete
  exact exists_stone_flow_of_esa smFullChain.op smFullChain.dense smFullChain.sym smFullChain.esa
