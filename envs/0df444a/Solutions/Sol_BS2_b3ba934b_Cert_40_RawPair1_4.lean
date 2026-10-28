-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_4
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:36:01.530383+00:00
-- url     : https://prove2.me/submissions/ec29867f-364e-4f0b-8163-6f3d294576fd

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_4
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 3)).eval profile1≤5840625979435819554426000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_4.raw_bound
