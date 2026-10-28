-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair2_0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:28:19.536007+00:00
-- url     : https://prove2.me/submissions/5785bad2-fad4-430d-8f51-40dd13eaddac

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair2_0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 2 0) (recipe 2 2)).eval profile2≤439022647791663747058857540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair2_0.raw_bound
