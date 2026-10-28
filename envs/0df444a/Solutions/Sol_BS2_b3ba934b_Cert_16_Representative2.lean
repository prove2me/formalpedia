-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_Representative2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:32:46.550001+00:00
-- url     : https://prove2.me/submissions/f81101c6-8b50-4bb3-8987-cee0c6894227

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_3
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_4
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_5
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_6
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (k : Fin 7) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 (BS2_b3ba934b_Cert_16_Aux2.representative2 k).1)
      (recipe 2 (BS2_b3ba934b_Cert_16_Aux2.representative2 k).2)).eval profile2≤BS2_b3ba934b_Cert_16_Aux2.representativeBound2 k := by
  fin_cases k
  · exact BS2_b3ba934b_Cert_16_RawPair2_0
  · exact BS2_b3ba934b_Cert_16_RawPair2_1
  · exact BS2_b3ba934b_Cert_16_RawPair2_2
  · exact BS2_b3ba934b_Cert_16_RawPair2_3
  · exact BS2_b3ba934b_Cert_16_RawPair2_4
  · exact BS2_b3ba934b_Cert_16_RawPair2_5
  · exact BS2_b3ba934b_Cert_16_RawPair2_6
