-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_29
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:49:28.168188+00:00
-- url     : https://prove2.me/submissions/0dfa2ce0-edcf-420b-b6cf-41cc64c0b716

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_29
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_29.raw_bound
