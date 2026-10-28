-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawPair3_4
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:31:35.085052+00:00
-- url     : https://prove2.me/submissions/88bbfe58-b086-4a4e-be26-04db146c8e16

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawPair3_4
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 0) (recipe 3 4)).eval profile3≤49435378198966834859642266240000000000000000000000000000000000000000000000 := by
  exact ThreeBoundMinmaxNumeric.Endpoint16.RawPair3_4.raw_bound
