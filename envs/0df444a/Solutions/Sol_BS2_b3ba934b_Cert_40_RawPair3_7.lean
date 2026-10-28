-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair3_7
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T07:04:17.817497+00:00
-- url     : https://prove2.me/submissions/f27b4a3f-a702-4c69-bb7f-5a387e939cd4

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair3_7
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 3 3) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair3_7.raw_bound
