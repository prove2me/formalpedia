-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_Representative0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:32:04.871123+00:00
-- url     : https://prove2.me/submissions/e9890299-09cb-427a-aa84-8af7138314aa

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_3
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_4
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (k : Fin 5) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 (BS2_b3ba934b_Cert_16_Aux0.representative0 k).1)
      (recipe 0 (BS2_b3ba934b_Cert_16_Aux0.representative0 k).2)).eval profile0≤BS2_b3ba934b_Cert_16_Aux0.representativeBound0 k := by
  fin_cases k
  · exact BS2_b3ba934b_Cert_16_RawPair0_0
  · exact BS2_b3ba934b_Cert_16_RawPair0_1
  · exact BS2_b3ba934b_Cert_16_RawPair0_2
  · exact BS2_b3ba934b_Cert_16_RawPair0_3
  · exact BS2_b3ba934b_Cert_16_RawPair0_4
