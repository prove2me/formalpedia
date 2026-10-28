-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_7
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:46:17.88291+00:00
-- url     : https://prove2.me/submissions/c503d937-d28f-4c53-acf0-4e4a22e9a68b

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_7
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 4)).eval profile1≤4440088403177649112679030000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_7.raw_bound
