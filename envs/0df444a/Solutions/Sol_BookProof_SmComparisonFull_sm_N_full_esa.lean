-- Prove2me | solution 1 for BookProof.SmComparisonFull.sm_N_full_esa
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:25:09.143846+00:00
-- url     : https://prove2.me/submissions/bfc9893f-383c-43bd-ba58-3aed696e06b6

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSmComparisonFull

open BookProof.FarisLavine
open BookProof.SmComparisonFull

noncomputable section

theorem solution : EssentiallySelfAdjointOn smFullChain.dom smFullChain.op :=
  smFullChain.esa
