-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_27
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:43:19.177981+00:00
-- url     : https://prove2.me/submissions/232cc172-0451-4f99-9e97-1f5ca691e949

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_27
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 9)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_27.raw_bound
