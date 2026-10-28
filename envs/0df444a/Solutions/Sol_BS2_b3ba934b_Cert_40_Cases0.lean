-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_Cases0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:48:49.454236+00:00
-- url     : https://prove2.me/submissions/a67ecf00-7189-4e5a-bcf6-ca442b48b8d2

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux0
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : ∀ i j : Fin 40, i≤j →
    0<(recipe 0 j).tolerance → (recipe 0 j).tolerance≤2 →
    recipe 0 i=recipe 0 (BS2_b3ba934b_Cert_40_Aux0.representative0 (BS2_b3ba934b_Cert_40_Aux0.caseIndex0 i j)).1 ∧
    recipe 0 j=recipe 0 (BS2_b3ba934b_Cert_40_Aux0.representative0 (BS2_b3ba934b_Cert_40_Aux0.caseIndex0 i j)).2 ∧
    BS2_b3ba934b_Cert_40_Aux0.representativeBound0 (BS2_b3ba934b_Cert_40_Aux0.caseIndex0 i j)≤rawProfile0 (.a i j) := by
  intro i
  fin_cases i <;> decide +kernel
