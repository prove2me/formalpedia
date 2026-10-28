-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair3_3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:51:17.534384+00:00
-- url     : https://prove2.me/submissions/7a8354fe-7a30-4c13-8d6e-1a0bc6301cc9

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair3_3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 3 3) (recipe 3 3)).eval profile3≤788367171188124766890095226590000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair3_3.raw_bound
