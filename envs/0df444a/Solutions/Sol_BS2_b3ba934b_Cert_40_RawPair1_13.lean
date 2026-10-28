-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_13
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:08:05.375856+00:00
-- url     : https://prove2.me/submissions/38baa8bb-fcc4-43fa-9c62-9a557c0ecb6a

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_13
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 5)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_13.raw_bound
