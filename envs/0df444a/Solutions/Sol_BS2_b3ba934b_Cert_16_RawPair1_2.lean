-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawPair1_2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:31:35.361321+00:00
-- url     : https://prove2.me/submissions/78896611-aab7-4c07-be3c-e2689395dcbd

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawPair1_2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 1 2) (recipe 1 2)).eval profile1≤192825632236769287372743000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundMinmaxNumeric.Endpoint16.RawPair1_2.raw_bound
