-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair0_3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:04:02.699906+00:00
-- url     : https://prove2.me/submissions/815f2e63-56e8-4c67-8d7b-bf4c8aa9e649

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 0 1) (recipe 0 2)).eval profile0≤59055514859764786074000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair0_3.raw_bound
