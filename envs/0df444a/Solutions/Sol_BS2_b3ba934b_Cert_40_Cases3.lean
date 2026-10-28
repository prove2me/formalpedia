-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_Cases3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:34:28.129379+00:00
-- url     : https://prove2.me/submissions/3d0b522a-9897-4d06-a3d7-9d73060ffe9d

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux3
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : ∀ i j : Fin 40, i≤j →
    0<(recipe 3 j).tolerance → (recipe 3 j).tolerance≤2 →
    recipe 3 i=recipe 3 (BS2_b3ba934b_Cert_40_Aux3.representative3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)).1 ∧
    recipe 3 j=recipe 3 (BS2_b3ba934b_Cert_40_Aux3.representative3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)).2 ∧
    BS2_b3ba934b_Cert_40_Aux3.representativeBound3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)≤rawProfile3 (.a i j) := by
  intro i
  fin_cases i <;> decide +kernel
