-- Prove2me | solution 2 for DetDLP.s8c_fp_pair_query
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:36:11.789354+00:00
-- url     : https://prove2.me/submissions/08484d29-530e-4388-9d1b-25a7f0d02f34

import Definitions.Def_DetDLP_S8L_MakePacket_v3
import Definitions.Def_DetDLP_S8L_PortEval

open DetDLP.S8L

theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [5] := by
  intro _
  apply FpPair.tagIntro MakePacket.make PortEval.port 800000 MakePacket.make_poly PortEval.port_poly
  intro p hp T S X η hT hη
  exact Bounds.realizes_of_eval η S X hT hη _ _ (MakePacket.make_word p T S X η)
    (PortEval.port_eval T S X η)
