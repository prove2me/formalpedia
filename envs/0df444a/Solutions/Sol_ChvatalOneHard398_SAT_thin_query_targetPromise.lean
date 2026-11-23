-- Prove2me | solution 1 for ChvatalOneHard398.SAT.thin_query_targetPromise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:16:25.429434+00:00
-- url     : https://prove2.me/submissions/7e81a318-3284-48ae-b8fb-1fd1b719f08d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding
import Theorems.Thm_ChvatalOneHard398_SAT_proposition_16
import Theorems.Thm_ChvatalOneHard398_SAT_satPolytope_isRationalPolyhedron

open CombOpt.ChvatalRank

theorem solution (F : ChvatalOneHard398.SAT.Formula) :
    ChvatalOneHard398.SAT.ThinQuery F → ChvatalOneHard398.SAT.TargetPromise F := by
  rintro ⟨a, ha, rfl, hthin⟩
  have h := ChvatalOneHard398.SAT.proposition_16.2 a ha
  refine ⟨h.1, h.2.1, (h.2.2.2.1 hthin).1 _ ?_ Set.Subset.rfl⟩
  exact ChvatalOneHard398.SAT.satPolytope_isRationalPolyhedron (ChvatalOneHard398.SAT.latticeFormula a)