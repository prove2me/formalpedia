-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_AChecked3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T07:31:08.350572+00:00
-- url     : https://prove2.me/submissions/c2d6e39a-33dc-4cb1-b7f8-b9c78f1e3697

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_Cases3
import Theorems.Thm_BS2_b3ba934b_Cert_40_Representative3
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther3
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (i j : Fin 40) (hij : i≤j) :
    (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j) := by
  by_cases hq : 0<(recipe 3 j).tolerance ∧ (recipe 3 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_40_Cases3 i j hij hq.1 hq.2
    calc
      _=(rawAExpr 40 caps records (recipe 3 (BS2_b3ba934b_Cert_40_Aux3.representative3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)).1)
          (recipe 3 (BS2_b3ba934b_Cert_40_Aux3.representative3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)).2)).eval profile3 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_40_Aux3.representativeBound3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j):=BS2_b3ba934b_Cert_40_Representative3 _
      _≤rawProfile3 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_40_RawOther3).1 i j hij (by omega)
