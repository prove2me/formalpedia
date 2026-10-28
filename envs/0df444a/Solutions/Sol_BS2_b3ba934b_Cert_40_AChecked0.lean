-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_AChecked0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:13:35.050611+00:00
-- url     : https://prove2.me/submissions/f1b9b6cc-9f12-4153-8673-fd50c23c7d08

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_Cases0
import Theorems.Thm_BS2_b3ba934b_Cert_40_Representative0
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther0
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (i j : Fin 40) (hij : i≤j) :
    (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j) := by
  by_cases hq : 0<(recipe 0 j).tolerance ∧ (recipe 0 j).tolerance≤2
  · obtain ⟨ha,hc,hb⟩:=BS2_b3ba934b_Cert_40_Cases0 i j hij hq.1 hq.2
    calc
      _=(rawAExpr 40 caps records (recipe 0 (BS2_b3ba934b_Cert_40_Aux0.representative0 (BS2_b3ba934b_Cert_40_Aux0.caseIndex0 i j)).1)
          (recipe 0 (BS2_b3ba934b_Cert_40_Aux0.representative0 (BS2_b3ba934b_Cert_40_Aux0.caseIndex0 i j)).2)).eval profile0 := by rw [ha,hc]
      _≤BS2_b3ba934b_Cert_40_Aux0.representativeBound0 (BS2_b3ba934b_Cert_40_Aux0.caseIndex0 i j):=BS2_b3ba934b_Cert_40_Representative0 _
      _≤rawProfile0 (.a i j):=hb
  · exact (BS2_b3ba934b_Cert_40_RawOther0).1 i j hij (by omega)
