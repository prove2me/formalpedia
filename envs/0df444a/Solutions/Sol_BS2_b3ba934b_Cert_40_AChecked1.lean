-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_AChecked1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:02:30.910945+00:00
-- url     : https://prove2.me/submissions/2d66e6f3-540d-453b-b88a-a2d4c39a1ae2

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_Cases1
import Theorems.Thm_BS2_b3ba934b_Cert_40_Representative1
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther1
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (i j : Fin 40) (hij : i≤j) :
    (rawAExpr 40 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j) := by
  by_cases hq : 0<(recipe 1 j).tolerance ∧ (recipe 1 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_40_Cases1 i j hij hq.1 hq.2
    calc
      _=(rawAExpr 40 caps records (recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)).1)
          (recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)).2)).eval profile1 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_40_Aux1.representativeBound1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j):=BS2_b3ba934b_Cert_40_Representative1 _
      _≤rawProfile1 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_40_RawOther1).1 i j hij (by omega)
