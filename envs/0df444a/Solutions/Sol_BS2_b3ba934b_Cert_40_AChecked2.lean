-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_AChecked2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:29:36.869082+00:00
-- url     : https://prove2.me/submissions/17ae9f93-aadf-40e5-9872-2c293bde7fcb

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_Cases2
import Theorems.Thm_BS2_b3ba934b_Cert_40_Representative2
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther2
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (i j : Fin 40) (hij : i≤j) :
    (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j) := by
  by_cases hq : 0<(recipe 2 j).tolerance ∧ (recipe 2 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_40_Cases2 i j hij hq.1 hq.2
    calc
      _=(rawAExpr 40 caps records (recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)).1)
          (recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)).2)).eval profile2 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_40_Aux2.representativeBound2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j):=BS2_b3ba934b_Cert_40_Representative2 _
      _≤rawProfile2 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_40_RawOther2).1 i j hij (by omega)
