-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_Cases2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:07:11.831699+00:00
-- url     : https://prove2.me/submissions/445fa122-2c40-4748-a715-268513a01e99

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux2
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : ∀ i j : Fin 40, i≤j →
    0<(recipe 2 j).tolerance → (recipe 2 j).tolerance≤2 →
    recipe 2 i=recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)).1 ∧
    recipe 2 j=recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)).2 ∧
    BS2_b3ba934b_Cert_40_Aux2.representativeBound2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)≤rawProfile2 (.a i j) := by
  intro i
  fin_cases i <;> decide +kernel
