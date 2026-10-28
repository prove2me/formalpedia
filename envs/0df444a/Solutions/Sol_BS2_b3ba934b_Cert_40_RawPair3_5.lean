-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair3_5
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:59:11.402194+00:00
-- url     : https://prove2.me/submissions/b6676846-d412-4047-95df-456d68ba23be

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair3_5
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 3 1) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair3_5.raw_bound
