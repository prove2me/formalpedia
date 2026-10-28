-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_40
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:32:19.858992+00:00
-- url     : https://prove2.me/submissions/2774f323-bb68-4f04-a2b6-e6233be18124

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_40
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 9) (recipe 1 10)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_40.raw_bound
