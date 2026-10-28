-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_Cases2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:32:31.008881+00:00
-- url     : https://prove2.me/submissions/c8219c16-d61e-4e97-adb6-42114ea61672

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux2
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution : ∀ i j : Fin 16, i≤j →
    0<(recipe 2 j).tolerance → (recipe 2 j).tolerance≤2 →
    recipe 2 i=recipe 2 (BS2_b3ba934b_Cert_16_Aux2.representative2 (BS2_b3ba934b_Cert_16_Aux2.caseIndex2 i j)).1 ∧
    recipe 2 j=recipe 2 (BS2_b3ba934b_Cert_16_Aux2.representative2 (BS2_b3ba934b_Cert_16_Aux2.caseIndex2 i j)).2 ∧
    BS2_b3ba934b_Cert_16_Aux2.representativeBound2 (BS2_b3ba934b_Cert_16_Aux2.caseIndex2 i j)≤rawProfile2 (.a i j) := by
  intro i
  fin_cases i <;> decide +kernel
