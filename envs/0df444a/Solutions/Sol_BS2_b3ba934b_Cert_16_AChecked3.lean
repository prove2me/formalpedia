-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_AChecked3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:55.40943+00:00
-- url     : https://prove2.me/submissions/0a3a09a8-10dc-4d16-89c3-fbf5177c54b3

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_Cases3
import Theorems.Thm_BS2_b3ba934b_Cert_16_Representative3
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther3
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (i j : Fin 16) (hij : i≤j) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j) := by
  by_cases hq : 0<(recipe 3 j).tolerance ∧ (recipe 3 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_16_Cases3 i j hij hq.1 hq.2
    calc
      _=(ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)).1)
          (recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)).2)).eval profile3 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_16_Aux3.representativeBound3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j):=BS2_b3ba934b_Cert_16_Representative3 _
      _≤rawProfile3 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_16_RawOther3).1 i j hij (by omega)
