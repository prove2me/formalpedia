-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_31
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:56:25.925996+00:00
-- url     : https://prove2.me/submissions/160f91fd-08b5-4c67-af9a-fe18d760c3be

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_31
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 7) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_31.raw_bound
