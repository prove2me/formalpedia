-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_Cases1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:18:58.375659+00:00
-- url     : https://prove2.me/submissions/f607aef8-c923-492d-8df7-405a22694d46

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux1
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : ∀ i j : Fin 40, i≤j →
    0<(recipe 1 j).tolerance → (recipe 1 j).tolerance≤2 →
    recipe 1 i=recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)).1 ∧
    recipe 1 j=recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)).2 ∧
    BS2_b3ba934b_Cert_40_Aux1.representativeBound1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)≤rawProfile1 (.a i j) := by
  intro i
  fin_cases i <;> decide +kernel
