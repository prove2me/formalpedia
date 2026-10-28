-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawPair0_1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:31:54.041992+00:00
-- url     : https://prove2.me/submissions/b64c7210-745f-4ce9-b506-707230035e35

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawPair0_1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 0 1) (recipe 0 1)).eval profile0≤2579858090809581183210000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundMinmaxNumeric.Endpoint16.RawPair0_1.raw_bound
