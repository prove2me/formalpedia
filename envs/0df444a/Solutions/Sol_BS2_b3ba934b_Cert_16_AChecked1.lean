-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_AChecked1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:44.75261+00:00
-- url     : https://prove2.me/submissions/08e7a928-41e4-4a44-9673-4bbc418592d9

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_Cases1
import Theorems.Thm_BS2_b3ba934b_Cert_16_Representative1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther1
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (i j : Fin 16) (hij : i≤j) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j) := by
  by_cases hq : 0<(recipe 1 j).tolerance ∧ (recipe 1 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_16_Cases1 i j hij hq.1 hq.2
    calc
      _=(ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 (BS2_b3ba934b_Cert_16_Aux1.representative1 (BS2_b3ba934b_Cert_16_Aux1.caseIndex1 i j)).1)
          (recipe 1 (BS2_b3ba934b_Cert_16_Aux1.representative1 (BS2_b3ba934b_Cert_16_Aux1.caseIndex1 i j)).2)).eval profile1 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_16_Aux1.representativeBound1 (BS2_b3ba934b_Cert_16_Aux1.caseIndex1 i j):=BS2_b3ba934b_Cert_16_Representative1 _
      _≤rawProfile1 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_16_RawOther1).1 i j hij (by omega)
