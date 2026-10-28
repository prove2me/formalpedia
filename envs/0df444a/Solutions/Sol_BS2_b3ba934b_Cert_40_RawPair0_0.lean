-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair0_0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:59:36.529311+00:00
-- url     : https://prove2.me/submissions/1bd5621e-6d49-4810-8e5b-5efb07b132fe

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 0 0) (recipe 0 1)).eval profile0≤77806142500417596074000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair0_0.raw_bound
