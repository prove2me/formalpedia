-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_AChecked2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:44.748542+00:00
-- url     : https://prove2.me/submissions/99994da8-c49b-48d8-a487-8791bff6a216

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_Cases2
import Theorems.Thm_BS2_b3ba934b_Cert_16_Representative2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther2
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (i j : Fin 16) (hij : i≤j) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j) := by
  by_cases hq : 0<(recipe 2 j).tolerance ∧ (recipe 2 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_16_Cases2 i j hij hq.1 hq.2
    calc
      _=(ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 (BS2_b3ba934b_Cert_16_Aux2.representative2 (BS2_b3ba934b_Cert_16_Aux2.caseIndex2 i j)).1)
          (recipe 2 (BS2_b3ba934b_Cert_16_Aux2.representative2 (BS2_b3ba934b_Cert_16_Aux2.caseIndex2 i j)).2)).eval profile2 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_16_Aux2.representativeBound2 (BS2_b3ba934b_Cert_16_Aux2.caseIndex2 i j):=BS2_b3ba934b_Cert_16_Representative2 _
      _≤rawProfile2 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_16_RawOther2).1 i j hij (by omega)
