-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair3_4
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:56:29.867499+00:00
-- url     : https://prove2.me/submissions/af115359-7dba-44da-b4f2-310712695644

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair3_4
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 3 0) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair3_4.raw_bound
