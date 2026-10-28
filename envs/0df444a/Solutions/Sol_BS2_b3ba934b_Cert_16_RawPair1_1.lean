-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawPair1_1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:31:35.447132+00:00
-- url     : https://prove2.me/submissions/cb46a379-a9ae-404e-876d-8cade1db21c1

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawPair1_1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 1 1) (recipe 1 2)).eval profile1≤11659749300103673188588500000000000000000000000000000000000000000000000 := by
  exact ThreeBoundMinmaxNumeric.Endpoint16.RawPair1_1.raw_bound
