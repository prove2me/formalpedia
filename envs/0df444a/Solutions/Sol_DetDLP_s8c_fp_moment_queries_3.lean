-- Prove2me | solution 3 for DetDLP.s8c_fp_moment_queries
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:51:26.256508+00:00
-- url     : https://prove2.me/submissions/637fda64-6706-4719-b223-1d5922babde2

import Definitions.Def_DetDLP_S8G_MakePoly
import Definitions.Def_DetDLP_S8G_PortEval

set_option autoImplicit false

theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [1] := by
  intro _
  apply DetDLP.S8G.FpMoment.tagIntro
    DetDLP.S8G.MakePacketV2.make DetDLP.S8G.PortEval.port 200000
    DetDLP.S8G.MakePacketV2.make_poly DetDLP.S8G.PortEval.port_poly
  intro p hp j T η hT hη
  exact DetDLP.S8G.Bounds.realizes_of_eval j η hT hη
    DetDLP.S8G.MakePacketV2.make DetDLP.S8G.PortEval.port
    (DetDLP.S8G.MakePacketV2.make_word p j T η
      (lt_of_lt_of_le (by decide : 0 < 2) (le_max_left ..)))
    (DetDLP.S8G.PortEval.port_eval p j T η)
