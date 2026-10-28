-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_Representative2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:02:22.383814+00:00
-- url     : https://prove2.me/submissions/cf399da4-a856-4d35-8148-94c19e029ead

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux2
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_0
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_1
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_2
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_3
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_4
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_5
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_6
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (k : Fin 7) :
    (rawAExpr 40 caps records (recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 k).1)
      (recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 k).2)).eval profile2≤BS2_b3ba934b_Cert_40_Aux2.representativeBound2 k := by
  fin_cases k
  · exact BS2_b3ba934b_Cert_40_RawPair2_0
  · exact BS2_b3ba934b_Cert_40_RawPair2_1
  · exact BS2_b3ba934b_Cert_40_RawPair2_2
  · exact BS2_b3ba934b_Cert_40_RawPair2_3
  · exact BS2_b3ba934b_Cert_40_RawPair2_4
  · exact BS2_b3ba934b_Cert_40_RawPair2_5
  · exact BS2_b3ba934b_Cert_40_RawPair2_6
