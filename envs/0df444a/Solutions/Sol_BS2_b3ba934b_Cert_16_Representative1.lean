-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_Representative1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:31:49.669252+00:00
-- url     : https://prove2.me/submissions/f95bf84c-3c8e-4265-bb09-c58791518c7a

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_3
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_4
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_5
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_6
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (k : Fin 7) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 (BS2_b3ba934b_Cert_16_Aux1.representative1 k).1)
      (recipe 1 (BS2_b3ba934b_Cert_16_Aux1.representative1 k).2)).eval profile1≤BS2_b3ba934b_Cert_16_Aux1.representativeBound1 k := by
  fin_cases k
  · exact BS2_b3ba934b_Cert_16_RawPair1_0
  · exact BS2_b3ba934b_Cert_16_RawPair1_1
  · exact BS2_b3ba934b_Cert_16_RawPair1_2
  · exact BS2_b3ba934b_Cert_16_RawPair1_3
  · exact BS2_b3ba934b_Cert_16_RawPair1_4
  · exact BS2_b3ba934b_Cert_16_RawPair1_5
  · exact BS2_b3ba934b_Cert_16_RawPair1_6
