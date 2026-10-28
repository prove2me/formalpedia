-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_21
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:16:21.77999+00:00
-- url     : https://prove2.me/submissions/08712ce9-3069-4a91-acec-f44585cd8d84

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_21
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 7)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_21.raw_bound
