-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_Representative3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:44.741981+00:00
-- url     : https://prove2.me/submissions/9d53cbc7-f59c-4578-a3c7-56ab29982960

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux3
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_3
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_4
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_5
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_6
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_7
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_8
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (k : Fin 9) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 k).1)
      (recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 k).2)).eval profile3≤BS2_b3ba934b_Cert_16_Aux3.representativeBound3 k := by
  fin_cases k
  · exact BS2_b3ba934b_Cert_16_RawPair3_0
  · exact BS2_b3ba934b_Cert_16_RawPair3_1
  · exact BS2_b3ba934b_Cert_16_RawPair3_2
  · exact BS2_b3ba934b_Cert_16_RawPair3_3
  · exact BS2_b3ba934b_Cert_16_RawPair3_4
  · exact BS2_b3ba934b_Cert_16_RawPair3_5
  · exact BS2_b3ba934b_Cert_16_RawPair3_6
  · exact BS2_b3ba934b_Cert_16_RawPair3_7
  · exact BS2_b3ba934b_Cert_16_RawPair3_8
