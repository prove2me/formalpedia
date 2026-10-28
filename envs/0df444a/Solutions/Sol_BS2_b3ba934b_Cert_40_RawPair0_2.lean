-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair0_2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:01:30.542205+00:00
-- url     : https://prove2.me/submissions/2fec8315-2462-46ab-8e57-0498b042d7c3

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 0 0) (recipe 0 2)).eval profile0≤59055514859764786074000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair0_2.raw_bound
