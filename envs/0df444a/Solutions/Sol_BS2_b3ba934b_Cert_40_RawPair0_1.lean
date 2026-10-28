-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair0_1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:57:05.769722+00:00
-- url     : https://prove2.me/submissions/9017eed1-10b1-44f2-b110-9e0f714e6c70

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 0 1) (recipe 0 1)).eval profile0≤1865036319175702176328000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair0_1.raw_bound
