-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_Representative1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:38:32.281985+00:00
-- url     : https://prove2.me/submissions/0119dec0-ae02-49fb-86f3-395b96d32ddc

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux1
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_0
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_1
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_2
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_3
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_4
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_5
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_6
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_7
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_8
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_9
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_10
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_11
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_12
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_13
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_14
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_15
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_16
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_17
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_18
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_19
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_20
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_21
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_22
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_23
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_24
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_25
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_26
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_27
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_28
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_29
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_30
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_31
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_32
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_33
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_34
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_35
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_36
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_37
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_38
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_39
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_40
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_41
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (k : Fin 42) :
    (rawAExpr 40 caps records (recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 k).1)
      (recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 k).2)).eval profile1≤BS2_b3ba934b_Cert_40_Aux1.representativeBound1 k := by
  fin_cases k
  · exact BS2_b3ba934b_Cert_40_RawPair1_0
  · exact BS2_b3ba934b_Cert_40_RawPair1_1
  · exact BS2_b3ba934b_Cert_40_RawPair1_2
  · exact BS2_b3ba934b_Cert_40_RawPair1_3
  · exact BS2_b3ba934b_Cert_40_RawPair1_4
  · exact BS2_b3ba934b_Cert_40_RawPair1_5
  · exact BS2_b3ba934b_Cert_40_RawPair1_6
  · exact BS2_b3ba934b_Cert_40_RawPair1_7
  · exact BS2_b3ba934b_Cert_40_RawPair1_8
  · exact BS2_b3ba934b_Cert_40_RawPair1_9
  · exact BS2_b3ba934b_Cert_40_RawPair1_10
  · exact BS2_b3ba934b_Cert_40_RawPair1_11
  · exact BS2_b3ba934b_Cert_40_RawPair1_12
  · exact BS2_b3ba934b_Cert_40_RawPair1_13
  · exact BS2_b3ba934b_Cert_40_RawPair1_14
  · exact BS2_b3ba934b_Cert_40_RawPair1_15
  · exact BS2_b3ba934b_Cert_40_RawPair1_16
  · exact BS2_b3ba934b_Cert_40_RawPair1_17
  · exact BS2_b3ba934b_Cert_40_RawPair1_18
  · exact BS2_b3ba934b_Cert_40_RawPair1_19
  · exact BS2_b3ba934b_Cert_40_RawPair1_20
  · exact BS2_b3ba934b_Cert_40_RawPair1_21
  · exact BS2_b3ba934b_Cert_40_RawPair1_22
  · exact BS2_b3ba934b_Cert_40_RawPair1_23
  · exact BS2_b3ba934b_Cert_40_RawPair1_24
  · exact BS2_b3ba934b_Cert_40_RawPair1_25
  · exact BS2_b3ba934b_Cert_40_RawPair1_26
  · exact BS2_b3ba934b_Cert_40_RawPair1_27
  · exact BS2_b3ba934b_Cert_40_RawPair1_28
  · exact BS2_b3ba934b_Cert_40_RawPair1_29
  · exact BS2_b3ba934b_Cert_40_RawPair1_30
  · exact BS2_b3ba934b_Cert_40_RawPair1_31
  · exact BS2_b3ba934b_Cert_40_RawPair1_32
  · exact BS2_b3ba934b_Cert_40_RawPair1_33
  · exact BS2_b3ba934b_Cert_40_RawPair1_34
  · exact BS2_b3ba934b_Cert_40_RawPair1_35
  · exact BS2_b3ba934b_Cert_40_RawPair1_36
  · exact BS2_b3ba934b_Cert_40_RawPair1_37
  · exact BS2_b3ba934b_Cert_40_RawPair1_38
  · exact BS2_b3ba934b_Cert_40_RawPair1_39
  · exact BS2_b3ba934b_Cert_40_RawPair1_40
  · exact BS2_b3ba934b_Cert_40_RawPair1_41
