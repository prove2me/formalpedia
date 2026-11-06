-- Prove2me | solution 2 for BookProof.FarisLavineOnly.outerHam_esa_fl
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:51:44.899664+00:00
-- url     : https://prove2.me/submissions/e6079dd9-bf6e-4e04-9114-e30b0c2b382a

import Definitions.Def_ChapterSqSumOuterFamily

open BookProof.FarisLavine BookProof.SqSumOuterFamily

theorem solution (F : SqFamily) :
    EssentiallySelfAdjointOn (outerCore F.dim) F.outerHam :=
  F.outerHam_esa
