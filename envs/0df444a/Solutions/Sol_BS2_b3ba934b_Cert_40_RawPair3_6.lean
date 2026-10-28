-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair3_6
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T07:01:42.136582+00:00
-- url     : https://prove2.me/submissions/889b53cc-13e7-4359-9b3e-e630c5a57c1c

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair3_6
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 3 2) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair3_6.raw_bound
