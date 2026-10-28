-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:29:47.793144+00:00
-- url     : https://prove2.me/submissions/91140c7d-3492-4a68-ae87-c4cc2c51e91a

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 2)).eval profile1≤139971226835560182197211160000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_2.raw_bound
