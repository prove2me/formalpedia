-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepDirect.WFam_iSupIndep
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:59:29.93199+00:00
-- url     : https://prove2.me/submissions/626da3a1-44bc-431f-95a9-4bbab61a1ee8

-- Generated from ChapterLorentzRealRepDirect.lean — solution of BookProof.ChapterLorentzRealRepDirect.WFam_iSupIndep
import Mathlib
import Definitions.Def_ChapterLorentzRealRepDirect
import Theorems.Thm_BookProof_ChapterLorentzRealRepDirect_WFam_isInternal
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRepFull
open BookProof.ChapterLorentzRealRepDirect



open Matrix Module


open BookProof.ChapterLorentzRealRep BookProof.ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepFull

set_option maxHeartbeats 1000000 in
theorem solution : iSupIndep WFam := WFam_isInternal.submodule_iSupIndep
