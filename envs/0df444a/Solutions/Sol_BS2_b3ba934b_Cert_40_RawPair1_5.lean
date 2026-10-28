-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_5
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:41:53.032415+00:00
-- url     : https://prove2.me/submissions/a732d741-926d-4172-808f-2a8ca42986c0

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_5
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 3)).eval profile1≤139965930438622964580062000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_5.raw_bound
