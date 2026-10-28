-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_Representative0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:08:41.445511+00:00
-- url     : https://prove2.me/submissions/5b3a8edb-a674-417c-976c-f345af9d4997

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux0
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_0
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_1
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_2
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_3
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_4
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (k : Fin 5) :
    (rawAExpr 40 caps records (recipe 0 (BS2_b3ba934b_Cert_40_Aux0.representative0 k).1)
      (recipe 0 (BS2_b3ba934b_Cert_40_Aux0.representative0 k).2)).eval profile0≤BS2_b3ba934b_Cert_40_Aux0.representativeBound0 k := by
  fin_cases k
  · exact BS2_b3ba934b_Cert_40_RawPair0_0
  · exact BS2_b3ba934b_Cert_40_RawPair0_1
  · exact BS2_b3ba934b_Cert_40_RawPair0_2
  · exact BS2_b3ba934b_Cert_40_RawPair0_3
  · exact BS2_b3ba934b_Cert_40_RawPair0_4
