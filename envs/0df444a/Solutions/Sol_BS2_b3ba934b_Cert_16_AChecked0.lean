-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_AChecked0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:32:46.565862+00:00
-- url     : https://prove2.me/submissions/cabfb376-d1e1-49ca-a3ed-c967d06e8662

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_Cases0
import Theorems.Thm_BS2_b3ba934b_Cert_16_Representative0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther0
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (i j : Fin 16) (hij : i≤j) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j) := by
  by_cases hq : 0<(recipe 0 j).tolerance ∧ (recipe 0 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_16_Cases0 i j hij hq.1 hq.2
    calc
      _=(ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 (BS2_b3ba934b_Cert_16_Aux0.representative0 (BS2_b3ba934b_Cert_16_Aux0.caseIndex0 i j)).1)
          (recipe 0 (BS2_b3ba934b_Cert_16_Aux0.representative0 (BS2_b3ba934b_Cert_16_Aux0.caseIndex0 i j)).2)).eval profile0 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_16_Aux0.representativeBound0 (BS2_b3ba934b_Cert_16_Aux0.caseIndex0 i j):=BS2_b3ba934b_Cert_16_Representative0 _
      _≤rawProfile0 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_16_RawOther0).1 i j hij (by omega)
