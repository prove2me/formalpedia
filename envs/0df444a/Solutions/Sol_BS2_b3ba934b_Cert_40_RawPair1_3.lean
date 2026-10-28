-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:33:51.003601+00:00
-- url     : https://prove2.me/submissions/dc2ac3a4-d94a-4790-b5c6-9be6f428b815

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 3)).eval profile1≤5840625979435819554426000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_3.raw_bound
