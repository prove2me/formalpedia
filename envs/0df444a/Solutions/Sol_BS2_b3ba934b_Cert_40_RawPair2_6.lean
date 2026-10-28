-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair2_6
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:59:29.073304+00:00
-- url     : https://prove2.me/submissions/c2b2037e-f480-45c4-9b04-5390fe39753c

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair2_6
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 2 3) (recipe 2 3)).eval profile2≤4560729516651630895596915310000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair2_6.raw_bound
